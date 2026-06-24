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
lean_object* l_USize_fromJson_x3f(lean_object*);
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
lean_object* l_Array_toJson___redArg(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Prod_toJson___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instFromJsonJson___lam__0(lean_object*);
lean_object* l_Prod_fromJson_x3f___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Option_fromJson_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_fromJson_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Option_toJson___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_toCtorIdx___boxed(lean_object*);
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
static const lean_closure_object l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_toCtorIdx(uint8_t v_x_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Lsp_RpcWireFormat_ctorIdx(v_x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_toCtorIdx___boxed(lean_object* v_x_42_){
_start:
{
uint8_t v_x_4__boxed_43_; lean_object* v_res_44_; 
v_x_4__boxed_43_ = lean_unbox(v_x_42_);
v_res_44_ = l_Lean_Lsp_RpcWireFormat_toCtorIdx(v_x_4__boxed_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_ctorElim___redArg(lean_object* v_k_45_){
_start:
{
lean_inc(v_k_45_);
return v_k_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_ctorElim___redArg___boxed(lean_object* v_k_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Lsp_RpcWireFormat_ctorElim___redArg(v_k_46_);
lean_dec(v_k_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_ctorElim(lean_object* v_motive_48_, lean_object* v_ctorIdx_49_, uint8_t v_t_50_, lean_object* v_h_51_, lean_object* v_k_52_){
_start:
{
lean_inc(v_k_52_);
return v_k_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_ctorElim___boxed(lean_object* v_motive_53_, lean_object* v_ctorIdx_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_k_57_){
_start:
{
uint8_t v_t_boxed_58_; lean_object* v_res_59_; 
v_t_boxed_58_ = lean_unbox(v_t_55_);
v_res_59_ = l_Lean_Lsp_RpcWireFormat_ctorElim(v_motive_53_, v_ctorIdx_54_, v_t_boxed_58_, v_h_56_, v_k_57_);
lean_dec(v_k_57_);
lean_dec(v_ctorIdx_54_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v0_elim___redArg(lean_object* v_v0_60_){
_start:
{
lean_inc(v_v0_60_);
return v_v0_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v0_elim___redArg___boxed(lean_object* v_v0_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Lsp_RpcWireFormat_v0_elim___redArg(v_v0_61_);
lean_dec(v_v0_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v0_elim(lean_object* v_motive_63_, uint8_t v_t_64_, lean_object* v_h_65_, lean_object* v_v0_66_){
_start:
{
lean_inc(v_v0_66_);
return v_v0_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v0_elim___boxed(lean_object* v_motive_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_v0_70_){
_start:
{
uint8_t v_t_boxed_71_; lean_object* v_res_72_; 
v_t_boxed_71_ = lean_unbox(v_t_68_);
v_res_72_ = l_Lean_Lsp_RpcWireFormat_v0_elim(v_motive_67_, v_t_boxed_71_, v_h_69_, v_v0_70_);
lean_dec(v_v0_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v1_elim___redArg(lean_object* v_v1_73_){
_start:
{
lean_inc(v_v1_73_);
return v_v1_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v1_elim___redArg___boxed(lean_object* v_v1_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Lsp_RpcWireFormat_v1_elim___redArg(v_v1_74_);
lean_dec(v_v1_74_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v1_elim(lean_object* v_motive_76_, uint8_t v_t_77_, lean_object* v_h_78_, lean_object* v_v1_79_){
_start:
{
lean_inc(v_v1_79_);
return v_v1_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v1_elim___boxed(lean_object* v_motive_80_, lean_object* v_t_81_, lean_object* v_h_82_, lean_object* v_v1_83_){
_start:
{
uint8_t v_t_boxed_84_; lean_object* v_res_85_; 
v_t_boxed_84_ = lean_unbox(v_t_81_);
v_res_85_ = l_Lean_Lsp_RpcWireFormat_v1_elim(v_motive_80_, v_t_boxed_84_, v_h_82_, v_v1_83_);
lean_dec(v_v1_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson(lean_object* v_json_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_Json_getTag_x3f(v_json_100_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v___x_102_; 
v___x_102_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__1));
return v___x_102_;
}
else
{
lean_object* v_val_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_val_103_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_val_103_);
lean_dec_ref_known(v___x_101_, 1);
v___x_104_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__2));
v___x_105_ = lean_string_dec_eq(v_val_103_, v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__3));
v___x_107_ = lean_string_dec_eq(v_val_103_, v___x_106_);
lean_dec(v_val_103_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
v___x_108_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__5));
return v___x_108_;
}
else
{
lean_object* v___x_109_; 
v___x_109_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__6));
return v___x_109_;
}
}
else
{
lean_object* v___x_110_; 
lean_dec(v_val_103_);
v___x_110_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__7));
return v___x_110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcWireFormat_toJson(uint8_t v_x_117_){
_start:
{
if (v_x_117_ == 0)
{
lean_object* v___x_118_; 
v___x_118_ = ((lean_object*)(l_Lean_Lsp_instToJsonRpcWireFormat_toJson___closed__0));
return v___x_118_;
}
else
{
lean_object* v___x_119_; 
v___x_119_ = ((lean_object*)(l_Lean_Lsp_instToJsonRpcWireFormat_toJson___closed__1));
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcWireFormat_toJson___boxed(lean_object* v_x_120_){
_start:
{
uint8_t v_x_44__boxed_121_; lean_object* v_res_122_; 
v_x_44__boxed_121_ = lean_unbox(v_x_120_);
v_res_122_ = l_Lean_Lsp_instToJsonRpcWireFormat_toJson(v_x_44__boxed_121_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_refFieldName(uint8_t v_x_127_){
_start:
{
if (v_x_127_ == 0)
{
lean_object* v___x_128_; 
v___x_128_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0));
return v___x_128_;
}
else
{
lean_object* v___x_129_; 
v___x_129_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1));
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_refFieldName___boxed(lean_object* v_x_130_){
_start:
{
uint8_t v_x_22__boxed_131_; lean_object* v_res_132_; 
v_x_22__boxed_131_ = lean_unbox(v_x_130_);
v_res_132_ = l_Lean_Lsp_RpcWireFormat_refFieldName(v_x_22__boxed_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef_default___redArg(lean_object* v_inst_133_){
_start:
{
size_t v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_usize_once(&l_Lean_Lsp_instInhabitedRpcRef_default___closed__0, &l_Lean_Lsp_instInhabitedRpcRef_default___closed__0_once, _init_l_Lean_Lsp_instInhabitedRpcRef_default___closed__0);
v___x_135_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_135_, 0, v_inst_133_);
lean_ctor_set_usize(v___x_135_, 1, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef_default(lean_object* v_00_u03b1_136_, lean_object* v_inst_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Server_instInhabitedWithRpcRef_default___redArg(v_inst_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef___redArg(lean_object* v_inst_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Lean_Server_instInhabitedWithRpcRef_default___redArg(v_inst_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef(lean_object* v_a_141_, lean_object* v_inst_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Server_instInhabitedWithRpcRef_default___redArg(v_inst_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = ((lean_object*)(l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn___boxed__const__1_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_));
v___x_148_ = lean_st_mk_ref(v___x_147_);
v___x_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2____boxed(lean_object* v_a_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_();
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_WithRpcRef_mk___redArg(lean_object* v_val_152_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; size_t v___x_156_; size_t v___x_157_; size_t v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; size_t v___x_162_; 
v___x_154_ = l_Lean_Server_freshWithRpcRefId;
v___x_155_ = lean_st_ref_take(v___x_154_);
v___x_156_ = ((size_t)1ULL);
v___x_157_ = lean_unbox_usize(v___x_155_);
v___x_158_ = lean_usize_add(v___x_157_, v___x_156_);
v___x_159_ = lean_box_usize(v___x_158_);
v___x_160_ = lean_st_ref_set(v___x_154_, v___x_159_);
v___x_161_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_161_, 0, v_val_152_);
v___x_162_ = lean_unbox_usize(v___x_155_);
lean_dec(v___x_155_);
lean_ctor_set_usize(v___x_161_, 1, v___x_162_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_WithRpcRef_mk___redArg___boxed(lean_object* v_val_163_, lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Server_WithRpcRef_mk___redArg(v_val_163_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_WithRpcRef_mk(lean_object* v_00_u03b1_166_, lean_object* v_val_167_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_Server_WithRpcRef_mk___redArg(v_val_167_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_WithRpcRef_mk___boxed(lean_object* v_00_u03b1_170_, lean_object* v_val_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Server_WithRpcRef_mk(v_00_u03b1_170_, v_val_171_);
return v_res_173_;
}
}
static lean_object* _init_l_Lean_Server_rpcStoreRef___redArg___closed__1(void){
_start:
{
lean_object* v___x_175_; lean_object* v___f_176_; 
v___x_175_ = lean_alloc_closure((void*)(l_instDecidableEqUSize___boxed), 2, 0);
v___f_176_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_176_, 0, v___x_175_);
return v___f_176_;
}
}
static lean_object* _init_l_Lean_Server_rpcStoreRef___redArg___closed__5(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_180_ = ((lean_object*)(l_Lean_Server_rpcStoreRef___redArg___closed__4));
v___x_181_ = lean_unsigned_to_nat(15u);
v___x_182_ = lean_unsigned_to_nat(132u);
v___x_183_ = ((lean_object*)(l_Lean_Server_rpcStoreRef___redArg___closed__3));
v___x_184_ = ((lean_object*)(l_Lean_Server_rpcStoreRef___redArg___closed__2));
v___x_185_ = l_mkPanicMessageWithDecl(v___x_184_, v___x_183_, v___x_182_, v___x_181_, v___x_180_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Server_rpcStoreRef___redArg___boxed__const__1(void){
_start:
{
size_t v___x_186_; lean_object* v___x_187_; 
v___x_186_ = l_Lean_Lsp_instInhabitedRpcRef_default;
v___x_187_ = lean_box_usize(v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcStoreRef___redArg(lean_object* v_inst_188_, lean_object* v_obj_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_aliveRefs_191_; lean_object* v_refsById_192_; size_t v_nextRef_193_; uint8_t v_wireFormat_194_; lean_object* v_val_195_; size_t v_id_196_; lean_object* v___f_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___f_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_aliveRefs_191_ = lean_ctor_get(v_a_190_, 0);
v_refsById_192_ = lean_ctor_get(v_a_190_, 1);
v_nextRef_193_ = lean_ctor_get_usize(v_a_190_, 2);
v_wireFormat_194_ = lean_ctor_get_uint8(v_a_190_, sizeof(void*)*3);
v_val_195_ = lean_ctor_get(v_obj_189_, 0);
v_id_196_ = lean_ctor_get_usize(v_obj_189_, 1);
v___f_197_ = ((lean_object*)(l_Lean_Server_rpcStoreRef___redArg___closed__0));
v___x_198_ = ((lean_object*)(l_Lean_Lsp_instBEqRpcRef___closed__0));
v___x_199_ = ((lean_object*)(l_Lean_Lsp_instHashableRpcRef___closed__0));
v___f_200_ = lean_obj_once(&l_Lean_Server_rpcStoreRef___redArg___closed__1, &l_Lean_Server_rpcStoreRef___redArg___closed__1_once, _init_l_Lean_Server_rpcStoreRef___redArg___closed__1);
v___x_201_ = lean_box_usize(v_id_196_);
v___x_202_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_200_, v___f_197_, v_refsById_192_, v___x_201_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_221_; 
lean_inc_ref(v_refsById_192_);
lean_inc_ref(v_aliveRefs_191_);
v_isSharedCheck_221_ = !lean_is_exclusive(v_a_190_);
if (v_isSharedCheck_221_ == 0)
{
lean_object* v_unused_222_; lean_object* v_unused_223_; 
v_unused_222_ = lean_ctor_get(v_a_190_, 1);
lean_dec(v_unused_222_);
v_unused_223_ = lean_ctor_get(v_a_190_, 0);
lean_dec(v_unused_223_);
v___x_204_ = v_a_190_;
v_isShared_205_ = v_isSharedCheck_221_;
goto v_resetjp_203_;
}
else
{
lean_dec(v_a_190_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_221_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; size_t v___x_214_; size_t v___x_215_; lean_object* v___x_217_; 
lean_inc(v_val_195_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v_inst_188_);
lean_ctor_set(v___x_206_, 1, v_val_195_);
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(v___x_208_, 0, v___x_206_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
lean_ctor_set_usize(v___x_208_, 2, v_id_196_);
v___x_209_ = lean_box_usize(v_nextRef_193_);
v___x_210_ = l_Lean_PersistentHashMap_insert___redArg(v___x_198_, v___x_199_, v_aliveRefs_191_, v___x_209_, v___x_208_);
v___x_211_ = lean_box_usize(v_id_196_);
v___x_212_ = lean_box_usize(v_nextRef_193_);
v___x_213_ = l_Lean_PersistentHashMap_insert___redArg(v___f_200_, v___f_197_, v_refsById_192_, v___x_211_, v___x_212_);
v___x_214_ = ((size_t)1ULL);
v___x_215_ = lean_usize_add(v_nextRef_193_, v___x_214_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v___x_213_);
lean_ctor_set(v___x_204_, 0, v___x_210_);
v___x_217_ = v___x_204_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v___x_213_);
lean_ctor_set_uint8(v_reuseFailAlloc_220_, sizeof(void*)*3, v_wireFormat_194_);
v___x_217_ = v_reuseFailAlloc_220_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
lean_ctor_set_usize(v___x_217_, 2, v___x_215_);
v___x_218_ = lean_box_usize(v_nextRef_193_);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v___x_217_);
return v___x_219_;
}
}
}
else
{
lean_object* v_val_224_; lean_object* v___x_225_; 
lean_dec(v_inst_188_);
v_val_224_ = lean_ctor_get(v___x_202_, 0);
lean_inc_n(v_val_224_, 2);
lean_dec_ref_known(v___x_202_, 1);
v___x_225_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_198_, v___x_199_, v_aliveRefs_191_, v_val_224_);
if (lean_obj_tag(v___x_225_) == 1)
{
lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_247_; 
lean_inc_ref(v_refsById_192_);
lean_inc_ref(v_aliveRefs_191_);
v_isSharedCheck_247_ = !lean_is_exclusive(v_a_190_);
if (v_isSharedCheck_247_ == 0)
{
lean_object* v_unused_248_; lean_object* v_unused_249_; 
v_unused_248_ = lean_ctor_get(v_a_190_, 1);
lean_dec(v_unused_248_);
v_unused_249_ = lean_ctor_get(v_a_190_, 0);
lean_dec(v_unused_249_);
v___x_227_ = v_a_190_;
v_isShared_228_ = v_isSharedCheck_247_;
goto v_resetjp_226_;
}
else
{
lean_dec(v_a_190_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_247_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v_val_229_; lean_object* v_obj_230_; size_t v_id_231_; lean_object* v_rc_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_246_; 
v_val_229_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_val_229_);
lean_dec_ref_known(v___x_225_, 1);
v_obj_230_ = lean_ctor_get(v_val_229_, 0);
v_id_231_ = lean_ctor_get_usize(v_val_229_, 2);
v_rc_232_ = lean_ctor_get(v_val_229_, 1);
v_isSharedCheck_246_ = !lean_is_exclusive(v_val_229_);
if (v_isSharedCheck_246_ == 0)
{
v___x_234_ = v_val_229_;
v_isShared_235_ = v_isSharedCheck_246_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_rc_232_);
lean_inc(v_obj_230_);
lean_dec(v_val_229_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_246_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = lean_nat_add(v_rc_232_, v___x_236_);
lean_dec(v_rc_232_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v___x_237_);
v___x_239_ = v___x_234_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_obj_230_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v___x_237_);
lean_ctor_set_usize(v_reuseFailAlloc_245_, 2, v_id_231_);
v___x_239_ = v_reuseFailAlloc_245_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
lean_inc(v_val_224_);
v___x_240_ = l_Lean_PersistentHashMap_insert___redArg(v___x_198_, v___x_199_, v_aliveRefs_191_, v_val_224_, v___x_239_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_240_);
v___x_242_ = v___x_227_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_refsById_192_);
lean_ctor_set_usize(v_reuseFailAlloc_244_, 2, v_nextRef_193_);
lean_ctor_set_uint8(v_reuseFailAlloc_244_, sizeof(void*)*3, v_wireFormat_194_);
v___x_242_ = v_reuseFailAlloc_244_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; 
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v_val_224_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
return v___x_243_;
}
}
}
}
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec(v___x_225_);
lean_dec(v_val_224_);
v___x_250_ = lean_obj_once(&l_Lean_Server_rpcStoreRef___redArg___closed__5, &l_Lean_Server_rpcStoreRef___redArg___closed__5_once, _init_l_Lean_Server_rpcStoreRef___redArg___closed__5);
v___x_251_ = l_Lean_Server_rpcStoreRef___redArg___boxed__const__1;
v___x_252_ = l_panic___redArg(v___x_251_, v___x_250_);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v_a_190_);
return v___x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcStoreRef___redArg___boxed(lean_object* v_inst_254_, lean_object* v_obj_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Server_rpcStoreRef___redArg(v_inst_254_, v_obj_255_, v_a_256_);
lean_dec_ref(v_obj_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcStoreRef(lean_object* v_00_u03b1_258_, lean_object* v_inst_259_, lean_object* v_obj_260_, lean_object* v_a_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_Server_rpcStoreRef___redArg(v_inst_259_, v_obj_260_, v_a_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcStoreRef___boxed(lean_object* v_00_u03b1_263_, lean_object* v_inst_264_, lean_object* v_obj_265_, lean_object* v_a_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_Server_rpcStoreRef(v_00_u03b1_263_, v_inst_264_, v_obj_265_, v_a_266_);
lean_dec_ref(v_obj_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcGetRef___redArg(lean_object* v_inst_275_, size_t v_r_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_aliveRefs_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_aliveRefs_278_ = lean_ctor_get(v_a_277_, 0);
v___x_279_ = ((lean_object*)(l_Lean_Lsp_instBEqRpcRef___closed__0));
v___x_280_ = ((lean_object*)(l_Lean_Lsp_instHashableRpcRef___closed__0));
v___x_281_ = lean_box_usize(v_r_276_);
v___x_282_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_279_, v___x_280_, v_aliveRefs_278_, v___x_281_);
if (lean_obj_tag(v___x_282_) == 1)
{
lean_object* v_val_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_320_; 
v_val_283_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_320_ == 0)
{
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_320_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_val_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_320_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v_obj_287_; size_t v_id_288_; lean_object* v___x_289_; 
v_obj_287_ = lean_ctor_get(v_val_283_, 0);
lean_inc(v_obj_287_);
v_id_288_ = lean_ctor_get_usize(v_val_283_, 2);
lean_dec(v_val_283_);
v___x_289_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_obj_287_, v_inst_275_);
if (lean_obj_tag(v___x_289_) == 1)
{
lean_object* v_val_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_298_; 
lean_dec(v_obj_287_);
lean_del_object(v___x_285_);
lean_dec(v_inst_275_);
v_val_290_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_298_ == 0)
{
v___x_292_ = v___x_289_;
v_isShared_293_ = v_isSharedCheck_298_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_val_290_);
lean_dec(v___x_289_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_298_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_294_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_294_, 0, v_val_290_);
lean_ctor_set_usize(v___x_294_, 1, v_id_288_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v___x_294_);
v___x_296_ = v___x_292_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
lean_dec(v___x_289_);
v___x_299_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__0));
v___x_300_ = lean_usize_to_nat(v_r_276_);
v___x_301_ = l_Nat_reprFast(v___x_300_);
v___x_302_ = lean_string_append(v___x_299_, v___x_301_);
lean_dec_ref(v___x_301_);
v___x_303_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__1));
v___x_304_ = lean_string_append(v___x_302_, v___x_303_);
v___x_305_ = 1;
v___x_306_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_inst_275_, v___x_305_);
v___x_307_ = lean_string_append(v___x_304_, v___x_306_);
lean_dec_ref(v___x_306_);
v___x_308_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__2));
v___x_309_ = lean_string_append(v___x_307_, v___x_308_);
v___x_310_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__3));
v___x_311_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_obj_287_);
lean_dec(v_obj_287_);
v___x_312_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_311_, v___x_305_);
v___x_313_ = lean_string_append(v___x_310_, v___x_312_);
lean_dec_ref(v___x_312_);
v___x_314_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__4));
v___x_315_ = lean_string_append(v___x_313_, v___x_314_);
v___x_316_ = lean_string_append(v___x_309_, v___x_315_);
lean_dec_ref(v___x_315_);
if (v_isShared_286_ == 0)
{
lean_ctor_set_tag(v___x_285_, 0);
lean_ctor_set(v___x_285_, 0, v___x_316_);
v___x_318_ = v___x_285_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
lean_dec(v___x_282_);
lean_dec(v_inst_275_);
v___x_321_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__5));
v___x_322_ = lean_usize_to_nat(v_r_276_);
v___x_323_ = l_Nat_reprFast(v___x_322_);
v___x_324_ = lean_string_append(v___x_321_, v___x_323_);
lean_dec_ref(v___x_323_);
v___x_325_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__6));
v___x_326_ = lean_string_append(v___x_324_, v___x_325_);
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcGetRef___redArg___boxed(lean_object* v_inst_328_, lean_object* v_r_329_, lean_object* v_a_330_){
_start:
{
size_t v_r_boxed_331_; lean_object* v_res_332_; 
v_r_boxed_331_ = lean_unbox_usize(v_r_329_);
lean_dec(v_r_329_);
v_res_332_ = l_Lean_Server_rpcGetRef___redArg(v_inst_328_, v_r_boxed_331_, v_a_330_);
lean_dec_ref(v_a_330_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcGetRef(lean_object* v_00_u03b1_333_, lean_object* v_inst_334_, size_t v_r_335_, lean_object* v_a_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Server_rpcGetRef___redArg(v_inst_334_, v_r_335_, v_a_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcGetRef___boxed(lean_object* v_00_u03b1_338_, lean_object* v_inst_339_, lean_object* v_r_340_, lean_object* v_a_341_){
_start:
{
size_t v_r_boxed_342_; lean_object* v_res_343_; 
v_r_boxed_342_ = lean_unbox_usize(v_r_340_);
lean_dec(v_r_340_);
v_res_343_ = l_Lean_Server_rpcGetRef(v_00_u03b1_338_, v_inst_339_, v_r_boxed_342_, v_a_341_);
lean_dec_ref(v_a_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11(lean_object* v_xs_344_, size_t v_v_345_, lean_object* v_i_346_){
_start:
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = lean_array_get_size(v_xs_344_);
v___x_348_ = lean_nat_dec_lt(v_i_346_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
lean_dec(v_i_346_);
v___x_349_ = lean_box(0);
return v___x_349_;
}
else
{
lean_object* v___x_350_; size_t v___x_351_; uint8_t v___x_352_; 
v___x_350_ = lean_array_fget_borrowed(v_xs_344_, v_i_346_);
v___x_351_ = lean_unbox_usize(v___x_350_);
v___x_352_ = lean_usize_dec_eq(v___x_351_, v_v_345_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_unsigned_to_nat(1u);
v___x_354_ = lean_nat_add(v_i_346_, v___x_353_);
lean_dec(v_i_346_);
v_i_346_ = v___x_354_;
goto _start;
}
else
{
lean_object* v___x_356_; 
v___x_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_356_, 0, v_i_346_);
return v___x_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11___boxed(lean_object* v_xs_357_, lean_object* v_v_358_, lean_object* v_i_359_){
_start:
{
size_t v_v_boxed_360_; lean_object* v_res_361_; 
v_v_boxed_360_ = lean_unbox_usize(v_v_358_);
lean_dec(v_v_358_);
v_res_361_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11(v_xs_357_, v_v_boxed_360_, v_i_359_);
lean_dec_ref(v_xs_357_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8(lean_object* v_xs_362_, size_t v_v_363_){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11(v_xs_362_, v_v_363_, v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8___boxed(lean_object* v_xs_366_, lean_object* v_v_367_){
_start:
{
size_t v_v_boxed_368_; lean_object* v_res_369_; 
v_v_boxed_368_ = lean_unbox_usize(v_v_367_);
lean_dec(v_v_367_);
v_res_369_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8(v_xs_366_, v_v_boxed_368_);
lean_dec_ref(v_xs_366_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(lean_object* v_x_370_, size_t v_x_371_, size_t v_x_372_){
_start:
{
if (lean_obj_tag(v_x_370_) == 0)
{
lean_object* v_es_373_; lean_object* v___x_374_; size_t v___x_375_; size_t v___x_376_; lean_object* v_j_377_; lean_object* v_entry_378_; 
v_es_373_ = lean_ctor_get(v_x_370_, 0);
v___x_374_ = lean_box(2);
v___x_375_ = ((size_t)31ULL);
v___x_376_ = lean_usize_land(v_x_371_, v___x_375_);
v_j_377_ = lean_usize_to_nat(v___x_376_);
v_entry_378_ = lean_array_get(v___x_374_, v_es_373_, v_j_377_);
switch(lean_obj_tag(v_entry_378_))
{
case 0:
{
lean_object* v_key_379_; size_t v___x_380_; uint8_t v___x_381_; 
v_key_379_ = lean_ctor_get(v_entry_378_, 0);
lean_inc(v_key_379_);
lean_dec_ref_known(v_entry_378_, 2);
v___x_380_ = lean_unbox_usize(v_key_379_);
lean_dec(v_key_379_);
v___x_381_ = lean_usize_dec_eq(v_x_372_, v___x_380_);
if (v___x_381_ == 0)
{
lean_dec(v_j_377_);
return v_x_370_;
}
else
{
lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_389_; 
lean_inc_ref(v_es_373_);
v_isSharedCheck_389_ = !lean_is_exclusive(v_x_370_);
if (v_isSharedCheck_389_ == 0)
{
lean_object* v_unused_390_; 
v_unused_390_ = lean_ctor_get(v_x_370_, 0);
lean_dec(v_unused_390_);
v___x_383_ = v_x_370_;
v_isShared_384_ = v_isSharedCheck_389_;
goto v_resetjp_382_;
}
else
{
lean_dec(v_x_370_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_389_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_385_ = lean_array_set(v_es_373_, v_j_377_, v___x_374_);
lean_dec(v_j_377_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_385_);
v___x_387_ = v___x_383_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
case 1:
{
lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_425_; 
lean_inc_ref(v_es_373_);
v_isSharedCheck_425_ = !lean_is_exclusive(v_x_370_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; 
v_unused_426_ = lean_ctor_get(v_x_370_, 0);
lean_dec(v_unused_426_);
v___x_392_ = v_x_370_;
v_isShared_393_ = v_isSharedCheck_425_;
goto v_resetjp_391_;
}
else
{
lean_dec(v_x_370_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_425_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v_node_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_424_; 
v_node_394_ = lean_ctor_get(v_entry_378_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v_entry_378_);
if (v_isSharedCheck_424_ == 0)
{
v___x_396_ = v_entry_378_;
v_isShared_397_ = v_isSharedCheck_424_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_node_394_);
lean_dec(v_entry_378_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_424_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
size_t v___x_398_; lean_object* v_entries_399_; size_t v___x_400_; lean_object* v_newNode_401_; lean_object* v___x_402_; 
v___x_398_ = ((size_t)5ULL);
v_entries_399_ = lean_array_set(v_es_373_, v_j_377_, v___x_374_);
v___x_400_ = lean_usize_shift_right(v_x_371_, v___x_398_);
v_newNode_401_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_node_394_, v___x_400_, v_x_372_);
lean_inc_ref(v_newNode_401_);
v___x_402_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_401_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v___x_404_; 
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v_newNode_401_);
v___x_404_ = v___x_396_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_newNode_401_);
v___x_404_ = v_reuseFailAlloc_409_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_405_ = lean_array_set(v_entries_399_, v_j_377_, v___x_404_);
lean_dec(v_j_377_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___x_405_);
v___x_407_ = v___x_392_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
else
{
lean_object* v_val_410_; lean_object* v_fst_411_; lean_object* v_snd_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_423_; 
lean_dec_ref(v_newNode_401_);
lean_del_object(v___x_396_);
v_val_410_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_val_410_);
lean_dec_ref_known(v___x_402_, 1);
v_fst_411_ = lean_ctor_get(v_val_410_, 0);
v_snd_412_ = lean_ctor_get(v_val_410_, 1);
v_isSharedCheck_423_ = !lean_is_exclusive(v_val_410_);
if (v_isSharedCheck_423_ == 0)
{
v___x_414_ = v_val_410_;
v_isShared_415_ = v_isSharedCheck_423_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_snd_412_);
lean_inc(v_fst_411_);
lean_dec(v_val_410_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_423_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_fst_411_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_snd_412_);
v___x_417_ = v_reuseFailAlloc_422_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_418_ = lean_array_set(v_entries_399_, v_j_377_, v___x_417_);
lean_dec(v_j_377_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___x_418_);
v___x_420_ = v___x_392_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_377_);
return v_x_370_;
}
}
}
else
{
lean_object* v_ks_427_; lean_object* v_vs_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_442_; 
v_ks_427_ = lean_ctor_get(v_x_370_, 0);
v_vs_428_ = lean_ctor_get(v_x_370_, 1);
v_isSharedCheck_442_ = !lean_is_exclusive(v_x_370_);
if (v_isSharedCheck_442_ == 0)
{
v___x_430_ = v_x_370_;
v_isShared_431_ = v_isSharedCheck_442_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_vs_428_);
lean_inc(v_ks_427_);
lean_dec(v_x_370_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_442_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; 
v___x_432_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8(v_ks_427_, v_x_372_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v___x_434_; 
if (v_isShared_431_ == 0)
{
v___x_434_ = v___x_430_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_ks_427_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_vs_428_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
else
{
lean_object* v_val_436_; lean_object* v_keys_x27_437_; lean_object* v_vals_x27_438_; lean_object* v___x_440_; 
v_val_436_ = lean_ctor_get(v___x_432_, 0);
lean_inc_n(v_val_436_, 2);
lean_dec_ref_known(v___x_432_, 1);
v_keys_x27_437_ = l_Array_eraseIdx___redArg(v_ks_427_, v_val_436_);
v_vals_x27_438_ = l_Array_eraseIdx___redArg(v_vs_428_, v_val_436_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 1, v_vals_x27_438_);
lean_ctor_set(v___x_430_, 0, v_keys_x27_437_);
v___x_440_ = v___x_430_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_keys_x27_437_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_vals_x27_438_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___boxed(lean_object* v_x_443_, lean_object* v_x_444_, lean_object* v_x_445_){
_start:
{
size_t v_x_1696__boxed_446_; size_t v_x_1697__boxed_447_; lean_object* v_res_448_; 
v_x_1696__boxed_446_ = lean_unbox_usize(v_x_444_);
lean_dec(v_x_444_);
v_x_1697__boxed_447_ = lean_unbox_usize(v_x_445_);
lean_dec(v_x_445_);
v_res_448_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_x_443_, v_x_1696__boxed_446_, v_x_1697__boxed_447_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(lean_object* v_x_449_, size_t v_x_450_){
_start:
{
uint64_t v___x_451_; size_t v_h_452_; lean_object* v___x_453_; 
v___x_451_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_450_);
v_h_452_ = lean_uint64_to_usize(v___x_451_);
v___x_453_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_x_449_, v_h_452_, v_x_450_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg___boxed(lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
size_t v_x_1834__boxed_456_; lean_object* v_res_457_; 
v_x_1834__boxed_456_ = lean_unbox_usize(v_x_455_);
lean_dec(v_x_455_);
v_res_457_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(v_x_454_, v_x_1834__boxed_456_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_458_, lean_object* v_vals_459_, lean_object* v_i_460_, size_t v_k_461_){
_start:
{
lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_462_ = lean_array_get_size(v_keys_458_);
v___x_463_ = lean_nat_dec_lt(v_i_460_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; 
lean_dec(v_i_460_);
v___x_464_ = lean_box(0);
return v___x_464_;
}
else
{
lean_object* v_k_x27_465_; size_t v___x_466_; uint8_t v___x_467_; 
v_k_x27_465_ = lean_array_fget_borrowed(v_keys_458_, v_i_460_);
v___x_466_ = lean_unbox_usize(v_k_x27_465_);
v___x_467_ = lean_usize_dec_eq(v_k_461_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = lean_nat_add(v_i_460_, v___x_468_);
lean_dec(v_i_460_);
v_i_460_ = v___x_469_;
goto _start;
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_array_fget_borrowed(v_vals_459_, v_i_460_);
lean_dec(v_i_460_);
lean_inc(v___x_471_);
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_473_, lean_object* v_vals_474_, lean_object* v_i_475_, lean_object* v_k_476_){
_start:
{
size_t v_k_boxed_477_; lean_object* v_res_478_; 
v_k_boxed_477_ = lean_unbox_usize(v_k_476_);
lean_dec(v_k_476_);
v_res_478_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(v_keys_473_, v_vals_474_, v_i_475_, v_k_boxed_477_);
lean_dec_ref(v_vals_474_);
lean_dec_ref(v_keys_473_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(lean_object* v_x_479_, size_t v_x_480_, size_t v_x_481_){
_start:
{
if (lean_obj_tag(v_x_479_) == 0)
{
lean_object* v_es_482_; lean_object* v___x_483_; size_t v___x_484_; size_t v___x_485_; lean_object* v_j_486_; lean_object* v___x_487_; 
v_es_482_ = lean_ctor_get(v_x_479_, 0);
v___x_483_ = lean_box(2);
v___x_484_ = ((size_t)31ULL);
v___x_485_ = lean_usize_land(v_x_480_, v___x_484_);
v_j_486_ = lean_usize_to_nat(v___x_485_);
v___x_487_ = lean_array_get_borrowed(v___x_483_, v_es_482_, v_j_486_);
lean_dec(v_j_486_);
switch(lean_obj_tag(v___x_487_))
{
case 0:
{
lean_object* v_key_488_; lean_object* v_val_489_; size_t v___x_490_; uint8_t v___x_491_; 
v_key_488_ = lean_ctor_get(v___x_487_, 0);
v_val_489_ = lean_ctor_get(v___x_487_, 1);
v___x_490_ = lean_unbox_usize(v_key_488_);
v___x_491_ = lean_usize_dec_eq(v_x_481_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; 
v___x_492_ = lean_box(0);
return v___x_492_;
}
else
{
lean_object* v___x_493_; 
lean_inc(v_val_489_);
v___x_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_493_, 0, v_val_489_);
return v___x_493_;
}
}
case 1:
{
lean_object* v_node_494_; size_t v___x_495_; size_t v___x_496_; 
v_node_494_ = lean_ctor_get(v___x_487_, 0);
v___x_495_ = ((size_t)5ULL);
v___x_496_ = lean_usize_shift_right(v_x_480_, v___x_495_);
v_x_479_ = v_node_494_;
v_x_480_ = v___x_496_;
goto _start;
}
default: 
{
lean_object* v___x_498_; 
v___x_498_ = lean_box(0);
return v___x_498_;
}
}
}
else
{
lean_object* v_ks_499_; lean_object* v_vs_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v_ks_499_ = lean_ctor_get(v_x_479_, 0);
v_vs_500_ = lean_ctor_get(v_x_479_, 1);
v___x_501_ = lean_unsigned_to_nat(0u);
v___x_502_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(v_ks_499_, v_vs_500_, v___x_501_, v_x_481_);
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg___boxed(lean_object* v_x_503_, lean_object* v_x_504_, lean_object* v_x_505_){
_start:
{
size_t v_x_1864__boxed_506_; size_t v_x_1865__boxed_507_; lean_object* v_res_508_; 
v_x_1864__boxed_506_ = lean_unbox_usize(v_x_504_);
lean_dec(v_x_504_);
v_x_1865__boxed_507_ = lean_unbox_usize(v_x_505_);
lean_dec(v_x_505_);
v_res_508_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_503_, v_x_1864__boxed_506_, v_x_1865__boxed_507_);
lean_dec_ref(v_x_503_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(lean_object* v_x_509_, size_t v_x_510_){
_start:
{
uint64_t v___x_511_; size_t v___x_512_; lean_object* v___x_513_; 
v___x_511_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_510_);
v___x_512_ = lean_uint64_to_usize(v___x_511_);
v___x_513_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_509_, v___x_512_, v_x_510_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg___boxed(lean_object* v_x_514_, lean_object* v_x_515_){
_start:
{
size_t v_x_1913__boxed_516_; lean_object* v_res_517_; 
v_x_1913__boxed_516_ = lean_unbox_usize(v_x_515_);
lean_dec(v_x_515_);
v_res_517_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(v_x_514_, v_x_1913__boxed_516_);
lean_dec_ref(v_x_514_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(lean_object* v_xs_518_, size_t v_v_519_, lean_object* v_i_520_){
_start:
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = lean_array_get_size(v_xs_518_);
v___x_522_ = lean_nat_dec_lt(v_i_520_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
lean_dec(v_i_520_);
v___x_523_ = lean_box(0);
return v___x_523_;
}
else
{
lean_object* v___x_524_; size_t v___x_525_; uint8_t v___x_526_; 
v___x_524_ = lean_array_fget_borrowed(v_xs_518_, v_i_520_);
v___x_525_ = lean_unbox_usize(v___x_524_);
v___x_526_ = lean_usize_dec_eq(v___x_525_, v_v_519_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_unsigned_to_nat(1u);
v___x_528_ = lean_nat_add(v_i_520_, v___x_527_);
lean_dec(v_i_520_);
v_i_520_ = v___x_528_;
goto _start;
}
else
{
lean_object* v___x_530_; 
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v_i_520_);
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14___boxed(lean_object* v_xs_531_, lean_object* v_v_532_, lean_object* v_i_533_){
_start:
{
size_t v_v_boxed_534_; lean_object* v_res_535_; 
v_v_boxed_534_ = lean_unbox_usize(v_v_532_);
lean_dec(v_v_532_);
v_res_535_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(v_xs_531_, v_v_boxed_534_, v_i_533_);
lean_dec_ref(v_xs_531_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(lean_object* v_xs_536_, size_t v_v_537_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(v_xs_536_, v_v_537_, v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11___boxed(lean_object* v_xs_540_, lean_object* v_v_541_){
_start:
{
size_t v_v_boxed_542_; lean_object* v_res_543_; 
v_v_boxed_542_ = lean_unbox_usize(v_v_541_);
lean_dec(v_v_541_);
v_res_543_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(v_xs_540_, v_v_boxed_542_);
lean_dec_ref(v_xs_540_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(lean_object* v_x_544_, size_t v_x_545_, size_t v_x_546_){
_start:
{
if (lean_obj_tag(v_x_544_) == 0)
{
lean_object* v_es_547_; lean_object* v___x_548_; size_t v___x_549_; size_t v___x_550_; lean_object* v_j_551_; lean_object* v_entry_552_; 
v_es_547_ = lean_ctor_get(v_x_544_, 0);
v___x_548_ = lean_box(2);
v___x_549_ = ((size_t)31ULL);
v___x_550_ = lean_usize_land(v_x_545_, v___x_549_);
v_j_551_ = lean_usize_to_nat(v___x_550_);
v_entry_552_ = lean_array_get(v___x_548_, v_es_547_, v_j_551_);
switch(lean_obj_tag(v_entry_552_))
{
case 0:
{
lean_object* v_key_553_; size_t v___x_554_; uint8_t v___x_555_; 
v_key_553_ = lean_ctor_get(v_entry_552_, 0);
lean_inc(v_key_553_);
lean_dec_ref_known(v_entry_552_, 2);
v___x_554_ = lean_unbox_usize(v_key_553_);
lean_dec(v_key_553_);
v___x_555_ = lean_usize_dec_eq(v_x_546_, v___x_554_);
if (v___x_555_ == 0)
{
lean_dec(v_j_551_);
return v_x_544_;
}
else
{
lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_563_; 
lean_inc_ref(v_es_547_);
v_isSharedCheck_563_ = !lean_is_exclusive(v_x_544_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; 
v_unused_564_ = lean_ctor_get(v_x_544_, 0);
lean_dec(v_unused_564_);
v___x_557_ = v_x_544_;
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
else
{
lean_dec(v_x_544_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_559_ = lean_array_set(v_es_547_, v_j_551_, v___x_548_);
lean_dec(v_j_551_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
case 1:
{
lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_599_; 
lean_inc_ref(v_es_547_);
v_isSharedCheck_599_ = !lean_is_exclusive(v_x_544_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; 
v_unused_600_ = lean_ctor_get(v_x_544_, 0);
lean_dec(v_unused_600_);
v___x_566_ = v_x_544_;
v_isShared_567_ = v_isSharedCheck_599_;
goto v_resetjp_565_;
}
else
{
lean_dec(v_x_544_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_599_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v_node_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_598_; 
v_node_568_ = lean_ctor_get(v_entry_552_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v_entry_552_);
if (v_isSharedCheck_598_ == 0)
{
v___x_570_ = v_entry_552_;
v_isShared_571_ = v_isSharedCheck_598_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_node_568_);
lean_dec(v_entry_552_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_598_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
size_t v___x_572_; lean_object* v_entries_573_; size_t v___x_574_; lean_object* v_newNode_575_; lean_object* v___x_576_; 
v___x_572_ = ((size_t)5ULL);
v_entries_573_ = lean_array_set(v_es_547_, v_j_551_, v___x_548_);
v___x_574_ = lean_usize_shift_right(v_x_545_, v___x_572_);
v_newNode_575_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_node_568_, v___x_574_, v_x_546_);
lean_inc_ref(v_newNode_575_);
v___x_576_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_575_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v___x_578_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v_newNode_575_);
v___x_578_ = v___x_570_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_newNode_575_);
v___x_578_ = v_reuseFailAlloc_583_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_579_ = lean_array_set(v_entries_573_, v_j_551_, v___x_578_);
lean_dec(v_j_551_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_579_);
v___x_581_ = v___x_566_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
else
{
lean_object* v_val_584_; lean_object* v_fst_585_; lean_object* v_snd_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_597_; 
lean_dec_ref(v_newNode_575_);
lean_del_object(v___x_570_);
v_val_584_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_val_584_);
lean_dec_ref_known(v___x_576_, 1);
v_fst_585_ = lean_ctor_get(v_val_584_, 0);
v_snd_586_ = lean_ctor_get(v_val_584_, 1);
v_isSharedCheck_597_ = !lean_is_exclusive(v_val_584_);
if (v_isSharedCheck_597_ == 0)
{
v___x_588_ = v_val_584_;
v_isShared_589_ = v_isSharedCheck_597_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_snd_586_);
lean_inc(v_fst_585_);
lean_dec(v_val_584_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_597_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_fst_585_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_snd_586_);
v___x_591_ = v_reuseFailAlloc_596_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_592_ = lean_array_set(v_entries_573_, v_j_551_, v___x_591_);
lean_dec(v_j_551_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_592_);
v___x_594_ = v___x_566_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_551_);
return v_x_544_;
}
}
}
else
{
lean_object* v_ks_601_; lean_object* v_vs_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_616_; 
v_ks_601_ = lean_ctor_get(v_x_544_, 0);
v_vs_602_ = lean_ctor_get(v_x_544_, 1);
v_isSharedCheck_616_ = !lean_is_exclusive(v_x_544_);
if (v_isSharedCheck_616_ == 0)
{
v___x_604_ = v_x_544_;
v_isShared_605_ = v_isSharedCheck_616_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_vs_602_);
lean_inc(v_ks_601_);
lean_dec(v_x_544_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_616_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; 
v___x_606_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(v_ks_601_, v_x_546_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v___x_608_; 
if (v_isShared_605_ == 0)
{
v___x_608_ = v___x_604_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_ks_601_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_vs_602_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
else
{
lean_object* v_val_610_; lean_object* v_keys_x27_611_; lean_object* v_vals_x27_612_; lean_object* v___x_614_; 
v_val_610_ = lean_ctor_get(v___x_606_, 0);
lean_inc_n(v_val_610_, 2);
lean_dec_ref_known(v___x_606_, 1);
v_keys_x27_611_ = l_Array_eraseIdx___redArg(v_ks_601_, v_val_610_);
v_vals_x27_612_ = l_Array_eraseIdx___redArg(v_vs_602_, v_val_610_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 1, v_vals_x27_612_);
lean_ctor_set(v___x_604_, 0, v_keys_x27_611_);
v___x_614_ = v___x_604_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_keys_x27_611_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_vals_x27_612_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg___boxed(lean_object* v_x_617_, lean_object* v_x_618_, lean_object* v_x_619_){
_start:
{
size_t v_x_1949__boxed_620_; size_t v_x_1950__boxed_621_; lean_object* v_res_622_; 
v_x_1949__boxed_620_ = lean_unbox_usize(v_x_618_);
lean_dec(v_x_618_);
v_x_1950__boxed_621_ = lean_unbox_usize(v_x_619_);
lean_dec(v_x_619_);
v_res_622_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_617_, v_x_1949__boxed_620_, v_x_1950__boxed_621_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(lean_object* v_x_623_, size_t v_x_624_){
_start:
{
uint64_t v___x_625_; size_t v_h_626_; lean_object* v___x_627_; 
v___x_625_ = lean_usize_to_uint64(v_x_624_);
v_h_626_ = lean_uint64_to_usize(v___x_625_);
v___x_627_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_623_, v_h_626_, v_x_624_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg___boxed(lean_object* v_x_628_, lean_object* v_x_629_){
_start:
{
size_t v_x_2087__boxed_630_; lean_object* v_res_631_; 
v_x_2087__boxed_630_ = lean_unbox_usize(v_x_629_);
lean_dec(v_x_629_);
v_res_631_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(v_x_628_, v_x_2087__boxed_630_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_x_632_, lean_object* v_x_633_, size_t v_x_634_, lean_object* v_x_635_){
_start:
{
lean_object* v_ks_636_; lean_object* v_vs_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_664_; 
v_ks_636_ = lean_ctor_get(v_x_632_, 0);
v_vs_637_ = lean_ctor_get(v_x_632_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v_x_632_);
if (v_isSharedCheck_664_ == 0)
{
v___x_639_ = v_x_632_;
v_isShared_640_ = v_isSharedCheck_664_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_vs_637_);
lean_inc(v_ks_636_);
lean_dec(v_x_632_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_664_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = lean_array_get_size(v_ks_636_);
v___x_642_ = lean_nat_dec_lt(v_x_633_, v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
lean_dec(v_x_633_);
v___x_643_ = lean_box_usize(v_x_634_);
v___x_644_ = lean_array_push(v_ks_636_, v___x_643_);
v___x_645_ = lean_array_push(v_vs_637_, v_x_635_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 1, v___x_645_);
lean_ctor_set(v___x_639_, 0, v___x_644_);
v___x_647_ = v___x_639_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
else
{
lean_object* v_k_x27_649_; size_t v___x_650_; uint8_t v___x_651_; 
v_k_x27_649_ = lean_array_fget_borrowed(v_ks_636_, v_x_633_);
v___x_650_ = lean_unbox_usize(v_k_x27_649_);
v___x_651_ = lean_usize_dec_eq(v_x_634_, v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_653_; 
if (v_isShared_640_ == 0)
{
v___x_653_ = v___x_639_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_ks_636_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_vs_637_);
v___x_653_ = v_reuseFailAlloc_657_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_unsigned_to_nat(1u);
v___x_655_ = lean_nat_add(v_x_633_, v___x_654_);
lean_dec(v_x_633_);
v_x_632_ = v___x_653_;
v_x_633_ = v___x_655_;
goto _start;
}
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_658_ = lean_box_usize(v_x_634_);
v___x_659_ = lean_array_fset(v_ks_636_, v_x_633_, v___x_658_);
v___x_660_ = lean_array_fset(v_vs_637_, v_x_633_, v_x_635_);
lean_dec(v_x_633_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 1, v___x_660_);
lean_ctor_set(v___x_639_, 0, v___x_659_);
v___x_662_ = v___x_639_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_x_665_, lean_object* v_x_666_, lean_object* v_x_667_, lean_object* v_x_668_){
_start:
{
size_t v_x_2098__boxed_669_; lean_object* v_res_670_; 
v_x_2098__boxed_669_ = lean_unbox_usize(v_x_667_);
lean_dec(v_x_667_);
v_res_670_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_x_665_, v_x_666_, v_x_2098__boxed_669_, v_x_668_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(lean_object* v_n_671_, size_t v_k_672_, lean_object* v_v_673_){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_n_671_, v___x_674_, v_k_672_, v_v_673_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_n_676_, lean_object* v_k_677_, lean_object* v_v_678_){
_start:
{
size_t v_k_boxed_679_; lean_object* v_res_680_; 
v_k_boxed_679_ = lean_unbox_usize(v_k_677_);
lean_dec(v_k_677_);
v_res_680_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v_n_676_, v_k_boxed_679_, v_v_678_);
return v_res_680_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(lean_object* v_x_682_, size_t v_x_683_, size_t v_x_684_, size_t v_x_685_, lean_object* v_x_686_){
_start:
{
if (lean_obj_tag(v_x_682_) == 0)
{
lean_object* v_es_687_; size_t v___x_688_; size_t v___x_689_; lean_object* v_j_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v_es_687_ = lean_ctor_get(v_x_682_, 0);
v___x_688_ = ((size_t)31ULL);
v___x_689_ = lean_usize_land(v_x_683_, v___x_688_);
v_j_690_ = lean_usize_to_nat(v___x_689_);
v___x_691_ = lean_array_get_size(v_es_687_);
v___x_692_ = lean_nat_dec_lt(v_j_690_, v___x_691_);
if (v___x_692_ == 0)
{
lean_dec(v_j_690_);
lean_dec(v_x_686_);
return v_x_682_;
}
else
{
lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_735_; 
lean_inc_ref(v_es_687_);
v_isSharedCheck_735_ = !lean_is_exclusive(v_x_682_);
if (v_isSharedCheck_735_ == 0)
{
lean_object* v_unused_736_; 
v_unused_736_ = lean_ctor_get(v_x_682_, 0);
lean_dec(v_unused_736_);
v___x_694_ = v_x_682_;
v_isShared_695_ = v_isSharedCheck_735_;
goto v_resetjp_693_;
}
else
{
lean_dec(v_x_682_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_735_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_v_696_; lean_object* v___x_697_; lean_object* v_xs_x27_698_; lean_object* v___y_700_; 
v_v_696_ = lean_array_fget(v_es_687_, v_j_690_);
v___x_697_ = lean_box(0);
v_xs_x27_698_ = lean_array_fset(v_es_687_, v_j_690_, v___x_697_);
switch(lean_obj_tag(v_v_696_))
{
case 0:
{
lean_object* v_key_705_; lean_object* v_val_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_719_; 
v_key_705_ = lean_ctor_get(v_v_696_, 0);
v_val_706_ = lean_ctor_get(v_v_696_, 1);
v_isSharedCheck_719_ = !lean_is_exclusive(v_v_696_);
if (v_isSharedCheck_719_ == 0)
{
v___x_708_ = v_v_696_;
v_isShared_709_ = v_isSharedCheck_719_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_val_706_);
lean_inc(v_key_705_);
lean_dec(v_v_696_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_719_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
size_t v___x_710_; uint8_t v___x_711_; 
v___x_710_ = lean_unbox_usize(v_key_705_);
v___x_711_ = lean_usize_dec_eq(v_x_685_, v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
lean_del_object(v___x_708_);
v___x_712_ = lean_box_usize(v_x_685_);
v___x_713_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_705_, v_val_706_, v___x_712_, v_x_686_);
v___x_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
v___y_700_ = v___x_714_;
goto v___jp_699_;
}
else
{
lean_object* v___x_715_; lean_object* v___x_717_; 
lean_dec(v_val_706_);
lean_dec(v_key_705_);
v___x_715_ = lean_box_usize(v_x_685_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v_x_686_);
lean_ctor_set(v___x_708_, 0, v___x_715_);
v___x_717_ = v___x_708_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_x_686_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
v___y_700_ = v___x_717_;
goto v___jp_699_;
}
}
}
}
case 1:
{
lean_object* v_node_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_732_; 
v_node_720_ = lean_ctor_get(v_v_696_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v_v_696_);
if (v_isSharedCheck_732_ == 0)
{
v___x_722_ = v_v_696_;
v_isShared_723_ = v_isSharedCheck_732_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_node_720_);
lean_dec(v_v_696_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_732_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
size_t v___x_724_; size_t v___x_725_; size_t v___x_726_; size_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_724_ = ((size_t)5ULL);
v___x_725_ = lean_usize_shift_right(v_x_683_, v___x_724_);
v___x_726_ = ((size_t)1ULL);
v___x_727_ = lean_usize_add(v_x_684_, v___x_726_);
v___x_728_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_node_720_, v___x_725_, v___x_727_, v_x_685_, v_x_686_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_728_);
v___x_730_ = v___x_722_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
v___y_700_ = v___x_730_;
goto v___jp_699_;
}
}
}
default: 
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_box_usize(v_x_685_);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v_x_686_);
v___y_700_ = v___x_734_;
goto v___jp_699_;
}
}
v___jp_699_:
{
lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_701_ = lean_array_fset(v_xs_x27_698_, v_j_690_, v___y_700_);
lean_dec(v_j_690_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_701_);
v___x_703_ = v___x_694_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
else
{
lean_object* v_ks_737_; lean_object* v_vs_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_758_; 
v_ks_737_ = lean_ctor_get(v_x_682_, 0);
v_vs_738_ = lean_ctor_get(v_x_682_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v_x_682_);
if (v_isSharedCheck_758_ == 0)
{
v___x_740_ = v_x_682_;
v_isShared_741_ = v_isSharedCheck_758_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_vs_738_);
lean_inc(v_ks_737_);
lean_dec(v_x_682_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_758_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_ks_737_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_vs_738_);
v___x_743_ = v_reuseFailAlloc_757_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v_newNode_744_; uint8_t v___y_746_; size_t v___x_752_; uint8_t v___x_753_; 
v_newNode_744_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v___x_743_, v_x_685_, v_x_686_);
v___x_752_ = ((size_t)7ULL);
v___x_753_ = lean_usize_dec_le(v___x_752_, v_x_684_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_754_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_744_);
v___x_755_ = lean_unsigned_to_nat(4u);
v___x_756_ = lean_nat_dec_lt(v___x_754_, v___x_755_);
lean_dec(v___x_754_);
v___y_746_ = v___x_756_;
goto v___jp_745_;
}
else
{
v___y_746_ = v___x_753_;
goto v___jp_745_;
}
v___jp_745_:
{
if (v___y_746_ == 0)
{
lean_object* v_ks_747_; lean_object* v_vs_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v_ks_747_ = lean_ctor_get(v_newNode_744_, 0);
lean_inc_ref(v_ks_747_);
v_vs_748_ = lean_ctor_get(v_newNode_744_, 1);
lean_inc_ref(v_vs_748_);
lean_dec_ref(v_newNode_744_);
v___x_749_ = lean_unsigned_to_nat(0u);
v___x_750_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0);
v___x_751_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_x_684_, v_ks_747_, v_vs_748_, v___x_749_, v___x_750_);
lean_dec_ref(v_vs_748_);
lean_dec_ref(v_ks_747_);
return v___x_751_;
}
else
{
return v_newNode_744_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(size_t v_depth_759_, lean_object* v_keys_760_, lean_object* v_vals_761_, lean_object* v_i_762_, lean_object* v_entries_763_){
_start:
{
lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_764_ = lean_array_get_size(v_keys_760_);
v___x_765_ = lean_nat_dec_lt(v_i_762_, v___x_764_);
if (v___x_765_ == 0)
{
lean_dec(v_i_762_);
return v_entries_763_;
}
else
{
lean_object* v_k_766_; lean_object* v_v_767_; size_t v___x_768_; uint64_t v___x_769_; size_t v_h_770_; size_t v___x_771_; lean_object* v___x_772_; size_t v___x_773_; size_t v___x_774_; size_t v___x_775_; size_t v_h_776_; lean_object* v___x_777_; size_t v___x_778_; lean_object* v___x_779_; 
v_k_766_ = lean_array_fget_borrowed(v_keys_760_, v_i_762_);
v_v_767_ = lean_array_fget_borrowed(v_vals_761_, v_i_762_);
v___x_768_ = lean_unbox_usize(v_k_766_);
v___x_769_ = l_Lean_Lsp_instHashableRpcRef_hash(v___x_768_);
v_h_770_ = lean_uint64_to_usize(v___x_769_);
v___x_771_ = ((size_t)5ULL);
v___x_772_ = lean_unsigned_to_nat(1u);
v___x_773_ = ((size_t)1ULL);
v___x_774_ = lean_usize_sub(v_depth_759_, v___x_773_);
v___x_775_ = lean_usize_mul(v___x_771_, v___x_774_);
v_h_776_ = lean_usize_shift_right(v_h_770_, v___x_775_);
v___x_777_ = lean_nat_add(v_i_762_, v___x_772_);
lean_dec(v_i_762_);
v___x_778_ = lean_unbox_usize(v_k_766_);
lean_inc(v_v_767_);
v___x_779_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_entries_763_, v_h_776_, v_depth_759_, v___x_778_, v_v_767_);
v_i_762_ = v___x_777_;
v_entries_763_ = v___x_779_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_781_, lean_object* v_keys_782_, lean_object* v_vals_783_, lean_object* v_i_784_, lean_object* v_entries_785_){
_start:
{
size_t v_depth_boxed_786_; lean_object* v_res_787_; 
v_depth_boxed_786_ = lean_unbox_usize(v_depth_781_);
lean_dec(v_depth_781_);
v_res_787_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_depth_boxed_786_, v_keys_782_, v_vals_783_, v_i_784_, v_entries_785_);
lean_dec_ref(v_vals_783_);
lean_dec_ref(v_keys_782_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___boxed(lean_object* v_x_788_, lean_object* v_x_789_, lean_object* v_x_790_, lean_object* v_x_791_, lean_object* v_x_792_){
_start:
{
size_t v_x_2183__boxed_793_; size_t v_x_2184__boxed_794_; size_t v_x_2185__boxed_795_; lean_object* v_res_796_; 
v_x_2183__boxed_793_ = lean_unbox_usize(v_x_789_);
lean_dec(v_x_789_);
v_x_2184__boxed_794_ = lean_unbox_usize(v_x_790_);
lean_dec(v_x_790_);
v_x_2185__boxed_795_ = lean_unbox_usize(v_x_791_);
lean_dec(v_x_791_);
v_res_796_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_788_, v_x_2183__boxed_793_, v_x_2184__boxed_794_, v_x_2185__boxed_795_, v_x_792_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(lean_object* v_x_797_, size_t v_x_798_, lean_object* v_x_799_){
_start:
{
uint64_t v___x_800_; size_t v___x_801_; size_t v___x_802_; lean_object* v___x_803_; 
v___x_800_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_798_);
v___x_801_ = lean_uint64_to_usize(v___x_800_);
v___x_802_ = ((size_t)1ULL);
v___x_803_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_797_, v___x_801_, v___x_802_, v_x_798_, v_x_799_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg___boxed(lean_object* v_x_804_, lean_object* v_x_805_, lean_object* v_x_806_){
_start:
{
size_t v_x_2351__boxed_807_; lean_object* v_res_808_; 
v_x_2351__boxed_807_ = lean_unbox_usize(v_x_805_);
lean_dec(v_x_805_);
v_res_808_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(v_x_804_, v_x_2351__boxed_807_, v_x_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcReleaseRef(size_t v_r_809_, lean_object* v_a_810_){
_start:
{
lean_object* v___y_812_; lean_object* v_aliveRefs_816_; lean_object* v_refsById_817_; size_t v_nextRef_818_; uint8_t v_wireFormat_819_; lean_object* v___x_820_; 
v_aliveRefs_816_ = lean_ctor_get(v_a_810_, 0);
v_refsById_817_ = lean_ctor_get(v_a_810_, 1);
v_nextRef_818_ = lean_ctor_get_usize(v_a_810_, 2);
v_wireFormat_819_ = lean_ctor_get_uint8(v_a_810_, sizeof(void*)*3);
v___x_820_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(v_aliveRefs_816_, v_r_809_);
if (lean_obj_tag(v___x_820_) == 1)
{
lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_848_; 
lean_inc_ref(v_refsById_817_);
lean_inc_ref(v_aliveRefs_816_);
v_isSharedCheck_848_ = !lean_is_exclusive(v_a_810_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; lean_object* v_unused_850_; 
v_unused_849_ = lean_ctor_get(v_a_810_, 1);
lean_dec(v_unused_849_);
v_unused_850_ = lean_ctor_get(v_a_810_, 0);
lean_dec(v_unused_850_);
v___x_822_ = v_a_810_;
v_isShared_823_ = v_isSharedCheck_848_;
goto v_resetjp_821_;
}
else
{
lean_dec(v_a_810_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_848_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v_val_824_; lean_object* v_obj_825_; size_t v_id_826_; lean_object* v_rc_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_847_; 
v_val_824_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_val_824_);
lean_dec_ref_known(v___x_820_, 1);
v_obj_825_ = lean_ctor_get(v_val_824_, 0);
v_id_826_ = lean_ctor_get_usize(v_val_824_, 2);
v_rc_827_ = lean_ctor_get(v_val_824_, 1);
v_isSharedCheck_847_ = !lean_is_exclusive(v_val_824_);
if (v_isSharedCheck_847_ == 0)
{
v___x_829_ = v_val_824_;
v_isShared_830_ = v_isSharedCheck_847_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_rc_827_);
lean_inc(v_obj_825_);
lean_dec(v_val_824_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_847_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_831_ = lean_unsigned_to_nat(1u);
v___x_832_ = lean_nat_sub(v_rc_827_, v___x_831_);
lean_dec(v_rc_827_);
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = lean_nat_dec_eq(v___x_832_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_836_; 
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 1, v___x_832_);
v___x_836_ = v___x_829_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_obj_825_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v___x_832_);
lean_ctor_set_usize(v_reuseFailAlloc_841_, 2, v_id_826_);
v___x_836_ = v_reuseFailAlloc_841_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_837_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(v_aliveRefs_816_, v_r_809_, v___x_836_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_837_);
v___x_839_ = v___x_822_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_refsById_817_);
lean_ctor_set_usize(v_reuseFailAlloc_840_, 2, v_nextRef_818_);
lean_ctor_set_uint8(v_reuseFailAlloc_840_, sizeof(void*)*3, v_wireFormat_819_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
v___y_812_ = v___x_839_;
goto v___jp_811_;
}
}
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
lean_dec(v___x_832_);
lean_del_object(v___x_829_);
lean_dec(v_obj_825_);
v___x_842_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(v_aliveRefs_816_, v_r_809_);
v___x_843_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(v_refsById_817_, v_id_826_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v___x_843_);
lean_ctor_set(v___x_822_, 0, v___x_842_);
v___x_845_ = v___x_822_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v___x_843_);
lean_ctor_set_usize(v_reuseFailAlloc_846_, 2, v_nextRef_818_);
lean_ctor_set_uint8(v_reuseFailAlloc_846_, sizeof(void*)*3, v_wireFormat_819_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
v___y_812_ = v___x_845_;
goto v___jp_811_;
}
}
}
}
}
else
{
uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec(v___x_820_);
v___x_851_ = 0;
v___x_852_ = lean_box(v___x_851_);
v___x_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
lean_ctor_set(v___x_853_, 1, v_a_810_);
return v___x_853_;
}
v___jp_811_:
{
uint8_t v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_813_ = 1;
v___x_814_ = lean_box(v___x_813_);
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
lean_ctor_set(v___x_815_, 1, v___y_812_);
return v___x_815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcReleaseRef___boxed(lean_object* v_r_854_, lean_object* v_a_855_){
_start:
{
size_t v_r_boxed_856_; lean_object* v_res_857_; 
v_r_boxed_856_ = lean_unbox_usize(v_r_854_);
lean_dec(v_r_854_);
v_res_857_ = l_Lean_Server_rpcReleaseRef(v_r_boxed_856_, v_a_855_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0(lean_object* v_00_u03b2_858_, lean_object* v_x_859_, size_t v_x_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(v_x_859_, v_x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___boxed(lean_object* v_00_u03b2_862_, lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
size_t v_x_2443__boxed_865_; lean_object* v_res_866_; 
v_x_2443__boxed_865_ = lean_unbox_usize(v_x_864_);
lean_dec(v_x_864_);
v_res_866_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0(v_00_u03b2_862_, v_x_863_, v_x_2443__boxed_865_);
lean_dec_ref(v_x_863_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1(lean_object* v_00_u03b2_867_, lean_object* v_x_868_, size_t v_x_869_, lean_object* v_x_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(v_x_868_, v_x_869_, v_x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___boxed(lean_object* v_00_u03b2_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
size_t v_x_2451__boxed_876_; lean_object* v_res_877_; 
v_x_2451__boxed_876_ = lean_unbox_usize(v_x_874_);
lean_dec(v_x_874_);
v_res_877_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1(v_00_u03b2_872_, v_x_873_, v_x_2451__boxed_876_, v_x_875_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2(lean_object* v_00_u03b2_878_, lean_object* v_x_879_, size_t v_x_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(v_x_879_, v_x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___boxed(lean_object* v_00_u03b2_882_, lean_object* v_x_883_, lean_object* v_x_884_){
_start:
{
size_t v_x_2462__boxed_885_; lean_object* v_res_886_; 
v_x_2462__boxed_885_ = lean_unbox_usize(v_x_884_);
lean_dec(v_x_884_);
v_res_886_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2(v_00_u03b2_882_, v_x_883_, v_x_2462__boxed_885_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3(lean_object* v_00_u03b2_887_, lean_object* v_x_888_, size_t v_x_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(v_x_888_, v_x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___boxed(lean_object* v_00_u03b2_891_, lean_object* v_x_892_, lean_object* v_x_893_){
_start:
{
size_t v_x_2470__boxed_894_; lean_object* v_res_895_; 
v_x_2470__boxed_894_ = lean_unbox_usize(v_x_893_);
lean_dec(v_x_893_);
v_res_895_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3(v_00_u03b2_891_, v_x_892_, v_x_2470__boxed_894_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0(lean_object* v_00_u03b2_896_, lean_object* v_x_897_, size_t v_x_898_, size_t v_x_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_897_, v_x_898_, v_x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___boxed(lean_object* v_00_u03b2_901_, lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_x_904_){
_start:
{
size_t v_x_2478__boxed_905_; size_t v_x_2479__boxed_906_; lean_object* v_res_907_; 
v_x_2478__boxed_905_ = lean_unbox_usize(v_x_903_);
lean_dec(v_x_903_);
v_x_2479__boxed_906_ = lean_unbox_usize(v_x_904_);
lean_dec(v_x_904_);
v_res_907_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0(v_00_u03b2_901_, v_x_902_, v_x_2478__boxed_905_, v_x_2479__boxed_906_);
lean_dec_ref(v_x_902_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2(lean_object* v_00_u03b2_908_, lean_object* v_x_909_, size_t v_x_910_, size_t v_x_911_, size_t v_x_912_, lean_object* v_x_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_909_, v_x_910_, v_x_911_, v_x_912_, v_x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___boxed(lean_object* v_00_u03b2_915_, lean_object* v_x_916_, lean_object* v_x_917_, lean_object* v_x_918_, lean_object* v_x_919_, lean_object* v_x_920_){
_start:
{
size_t v_x_2489__boxed_921_; size_t v_x_2490__boxed_922_; size_t v_x_2491__boxed_923_; lean_object* v_res_924_; 
v_x_2489__boxed_921_ = lean_unbox_usize(v_x_917_);
lean_dec(v_x_917_);
v_x_2490__boxed_922_ = lean_unbox_usize(v_x_918_);
lean_dec(v_x_918_);
v_x_2491__boxed_923_ = lean_unbox_usize(v_x_919_);
lean_dec(v_x_919_);
v_res_924_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2(v_00_u03b2_915_, v_x_916_, v_x_2489__boxed_921_, v_x_2490__boxed_922_, v_x_2491__boxed_923_, v_x_920_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4(lean_object* v_00_u03b2_925_, lean_object* v_x_926_, size_t v_x_927_, size_t v_x_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_x_926_, v_x_927_, v_x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___boxed(lean_object* v_00_u03b2_930_, lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v_x_933_){
_start:
{
size_t v_x_2506__boxed_934_; size_t v_x_2507__boxed_935_; lean_object* v_res_936_; 
v_x_2506__boxed_934_ = lean_unbox_usize(v_x_932_);
lean_dec(v_x_932_);
v_x_2507__boxed_935_ = lean_unbox_usize(v_x_933_);
lean_dec(v_x_933_);
v_res_936_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4(v_00_u03b2_930_, v_x_931_, v_x_2506__boxed_934_, v_x_2507__boxed_935_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6(lean_object* v_00_u03b2_937_, lean_object* v_x_938_, size_t v_x_939_, size_t v_x_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_938_, v_x_939_, v_x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___boxed(lean_object* v_00_u03b2_942_, lean_object* v_x_943_, lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
size_t v_x_2517__boxed_946_; size_t v_x_2518__boxed_947_; lean_object* v_res_948_; 
v_x_2517__boxed_946_ = lean_unbox_usize(v_x_944_);
lean_dec(v_x_944_);
v_x_2518__boxed_947_ = lean_unbox_usize(v_x_945_);
lean_dec(v_x_945_);
v_res_948_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6(v_00_u03b2_942_, v_x_943_, v_x_2517__boxed_946_, v_x_2518__boxed_947_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_949_, lean_object* v_keys_950_, lean_object* v_vals_951_, lean_object* v_heq_952_, lean_object* v_i_953_, size_t v_k_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(v_keys_950_, v_vals_951_, v_i_953_, v_k_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_956_, lean_object* v_keys_957_, lean_object* v_vals_958_, lean_object* v_heq_959_, lean_object* v_i_960_, lean_object* v_k_961_){
_start:
{
size_t v_k_boxed_962_; lean_object* v_res_963_; 
v_k_boxed_962_ = lean_unbox_usize(v_k_961_);
lean_dec(v_k_961_);
v_res_963_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1(v_00_u03b2_956_, v_keys_957_, v_vals_958_, v_heq_959_, v_i_960_, v_k_boxed_962_);
lean_dec_ref(v_vals_958_);
lean_dec_ref(v_keys_957_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_964_, lean_object* v_n_965_, size_t v_k_966_, lean_object* v_v_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v_n_965_, v_k_966_, v_v_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_969_, lean_object* v_n_970_, lean_object* v_k_971_, lean_object* v_v_972_){
_start:
{
size_t v_k_boxed_973_; lean_object* v_res_974_; 
v_k_boxed_973_ = lean_unbox_usize(v_k_971_);
lean_dec(v_k_971_);
v_res_974_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4(v_00_u03b2_969_, v_n_970_, v_k_boxed_973_, v_v_972_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_975_, size_t v_depth_976_, lean_object* v_keys_977_, lean_object* v_vals_978_, lean_object* v_heq_979_, lean_object* v_i_980_, lean_object* v_entries_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_depth_976_, v_keys_977_, v_vals_978_, v_i_980_, v_entries_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_983_, lean_object* v_depth_984_, lean_object* v_keys_985_, lean_object* v_vals_986_, lean_object* v_heq_987_, lean_object* v_i_988_, lean_object* v_entries_989_){
_start:
{
size_t v_depth_boxed_990_; lean_object* v_res_991_; 
v_depth_boxed_990_ = lean_unbox_usize(v_depth_984_);
lean_dec(v_depth_984_);
v_res_991_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5(v_00_u03b2_983_, v_depth_boxed_990_, v_keys_985_, v_vals_986_, v_heq_987_, v_i_988_, v_entries_989_);
lean_dec_ref(v_vals_986_);
lean_dec_ref(v_keys_985_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_992_, lean_object* v_x_993_, lean_object* v_x_994_, size_t v_x_995_, lean_object* v_x_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_x_993_, v_x_994_, v_x_995_, v_x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_998_, lean_object* v_x_999_, lean_object* v_x_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_){
_start:
{
size_t v_x_2535__boxed_1003_; lean_object* v_res_1004_; 
v_x_2535__boxed_1003_ = lean_unbox_usize(v_x_1001_);
lean_dec(v_x_1001_);
v_res_1004_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7(v_00_u03b2_998_, v_x_999_, v_x_1000_, v_x_2535__boxed_1003_, v_x_1002_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__0(lean_object* v_inst_1005_, lean_object* v_a_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = lean_apply_1(v_inst_1005_, v_a_1006_);
v___x_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v___y_1007_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1(lean_object* v_inst_1010_, lean_object* v___x_1011_, lean_object* v___x_1012_, lean_object* v_j_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_201__overap_1016_; lean_object* v___x_1017_; 
v___x_1015_ = lean_apply_1(v_inst_1010_, v_j_1013_);
v___x_201__overap_1016_ = l_MonadExcept_ofExcept___redArg(v___x_1011_, v___x_1012_, v___x_1015_);
lean_inc_ref(v___y_1014_);
v___x_1017_ = lean_apply_1(v___x_201__overap_1016_, v___y_1014_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1___boxed(lean_object* v_inst_1018_, lean_object* v___x_1019_, lean_object* v___x_1020_, lean_object* v_j_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1(v_inst_1018_, v___x_1019_, v___x_1020_, v_j_1021_, v___y_1022_);
lean_dec_ref(v___y_1022_);
return v_res_1023_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9));
v___x_1044_ = l_ReaderT_instMonad___redArg(v___x_1043_);
return v___x_1044_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___f_1046_; 
v___x_1045_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___f_1046_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1046_, 0, v___x_1045_);
return v___f_1046_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___f_1048_; 
v___x_1047_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___f_1048_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_1048_, 0, v___x_1047_);
return v___f_1048_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___f_1050_; 
v___x_1049_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___f_1050_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_1050_, 0, v___x_1049_);
return v___f_1050_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___f_1052_; 
v___x_1051_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___f_1052_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_1052_, 0, v___x_1051_);
return v___f_1052_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1054_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_1054_, 0, lean_box(0));
lean_closure_set(v___x_1054_, 1, lean_box(0));
lean_closure_set(v___x_1054_, 2, v___x_1053_);
return v___x_1054_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16(void){
_start:
{
lean_object* v___f_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___f_1055_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11);
v___x_1056_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15);
v___x_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v___f_1055_);
return v___x_1057_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1059_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_1059_, 0, lean_box(0));
lean_closure_set(v___x_1059_, 1, lean_box(0));
lean_closure_set(v___x_1059_, 2, v___x_1058_);
return v___x_1059_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18(void){
_start:
{
lean_object* v___f_1060_; lean_object* v___f_1061_; lean_object* v___f_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___f_1060_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14);
v___f_1061_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13);
v___f_1062_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12);
v___x_1063_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17);
v___x_1064_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16);
v___x_1065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v___x_1063_);
lean_ctor_set(v___x_1065_, 2, v___f_1062_);
lean_ctor_set(v___x_1065_, 3, v___f_1061_);
lean_ctor_set(v___x_1065_, 4, v___f_1060_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1067_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_1067_, 0, lean_box(0));
lean_closure_set(v___x_1067_, 1, lean_box(0));
lean_closure_set(v___x_1067_, 2, v___x_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19);
v___x_1069_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___x_1068_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1072_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch), 6, 3);
lean_closure_set(v___x_1072_, 0, lean_box(0));
lean_closure_set(v___x_1072_, 1, lean_box(0));
lean_closure_set(v___x_1072_, 2, v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg(lean_object* v_inst_1073_, lean_object* v_inst_1074_){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v_toApplicative_1077_; lean_object* v_toPure_1078_; lean_object* v___f_1079_; lean_object* v___f_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___f_1084_; lean_object* v___x_1085_; 
v___x_1075_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1076_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20);
v_toApplicative_1077_ = lean_ctor_get(v___x_1075_, 0);
v_toPure_1078_ = lean_ctor_get(v_toApplicative_1077_, 1);
v___f_1079_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1079_, 0, v_inst_1074_);
lean_inc(v_toPure_1078_);
v___f_1080_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptTOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1080_, 0, v_toPure_1078_);
v___x_1081_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21);
v___x_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___f_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_1082_);
v___f_1084_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1084_, 0, v_inst_1073_);
lean_closure_set(v___f_1084_, 1, v___x_1076_);
lean_closure_set(v___f_1084_, 2, v___x_1083_);
v___x_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___f_1079_);
lean_ctor_set(v___x_1085_, 1, v___f_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson(lean_object* v_00_u03b1_1086_, lean_object* v_inst_1087_, lean_object* v_inst_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg(v_inst_1087_, v_inst_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg___lam__0(lean_object* v_inst_1090_, lean_object* v___x_1091_, lean_object* v_v_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_fst_1095_; lean_object* v_snd_1096_; 
if (lean_obj_tag(v_v_1092_) == 0)
{
lean_object* v___x_1099_; 
lean_dec_ref(v_inst_1090_);
v___x_1099_ = lean_box(0);
v_fst_1095_ = v___x_1099_;
v_snd_1096_ = v___y_1093_;
goto v___jp_1094_;
}
else
{
lean_object* v_rpcEncode_1100_; lean_object* v_val_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1111_; 
v_rpcEncode_1100_ = lean_ctor_get(v_inst_1090_, 0);
lean_inc_ref(v_rpcEncode_1100_);
lean_dec_ref(v_inst_1090_);
v_val_1101_ = lean_ctor_get(v_v_1092_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_v_1092_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1103_ = v_v_1092_;
v_isShared_1104_ = v_isSharedCheck_1111_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_val_1101_);
lean_dec(v_v_1092_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1111_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1105_; lean_object* v_fst_1106_; lean_object* v_snd_1107_; lean_object* v___x_1109_; 
v___x_1105_ = lean_apply_2(v_rpcEncode_1100_, v_val_1101_, v___y_1093_);
v_fst_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_fst_1106_);
v_snd_1107_ = lean_ctor_get(v___x_1105_, 1);
lean_inc(v_snd_1107_);
lean_dec_ref(v___x_1105_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v_fst_1106_);
v___x_1109_ = v___x_1103_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_fst_1106_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
v_fst_1095_ = v___x_1109_;
v_snd_1096_ = v_snd_1107_;
goto v___jp_1094_;
}
}
}
v___jp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = l_Option_toJson___redArg(v___x_1091_, v_fst_1095_);
v___x_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v_snd_1096_);
return v___x_1098_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg___lam__1(lean_object* v___f_1114_, lean_object* v_inst_1115_, lean_object* v_j_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Option_fromJson_x3f___redArg(v___f_1114_, v_j_1116_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec_ref(v_inst_1115_);
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
else
{
lean_object* v_a_1127_; 
v_a_1127_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1127_);
lean_dec_ref_known(v___x_1118_, 1);
if (lean_obj_tag(v_a_1127_) == 0)
{
lean_object* v___x_1128_; 
lean_dec_ref(v_inst_1115_);
v___x_1128_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___lam__1___closed__0));
return v___x_1128_;
}
else
{
lean_object* v_rpcDecode_1129_; lean_object* v_val_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1154_; 
v_rpcDecode_1129_ = lean_ctor_get(v_inst_1115_, 1);
lean_inc_ref(v_rpcDecode_1129_);
lean_dec_ref(v_inst_1115_);
v_val_1130_ = lean_ctor_get(v_a_1127_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_a_1127_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1132_ = v_a_1127_;
v_isShared_1133_ = v_isSharedCheck_1154_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_val_1130_);
lean_dec(v_a_1127_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1154_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; 
lean_inc_ref(v___y_1117_);
v___x_1134_ = lean_apply_2(v_rpcDecode_1129_, v_val_1130_, v___y_1117_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_del_object(v___x_1132_);
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1153_; 
v_a_1143_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1145_ = v___x_1134_;
v_isShared_1146_ = v_isSharedCheck_1153_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1134_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1153_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v_a_1143_);
v___x_1148_ = v___x_1132_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1150_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1148_);
v___x_1150_ = v___x_1145_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg___lam__1___boxed(lean_object* v___f_1155_, lean_object* v_inst_1156_, lean_object* v_j_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_Server_instRpcEncodableOption___redArg___lam__1(v___f_1155_, v_inst_1156_, v_j_1157_, v___y_1158_);
lean_dec_ref(v___y_1158_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg(lean_object* v_inst_1162_){
_start:
{
lean_object* v___x_1163_; lean_object* v___f_1164_; lean_object* v___f_1165_; lean_object* v___f_1166_; lean_object* v___x_1167_; 
v___x_1163_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__0));
lean_inc_ref(v_inst_1162_);
v___f_1164_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOption___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1164_, 0, v_inst_1162_);
lean_closure_set(v___f_1164_, 1, v___x_1163_);
v___f_1165_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__1));
v___f_1166_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOption___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1166_, 0, v___f_1165_);
lean_closure_set(v___f_1166_, 1, v_inst_1162_);
v___x_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___f_1164_);
lean_ctor_set(v___x_1167_, 1, v___f_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption(lean_object* v_00_u03b1_1168_, lean_object* v_inst_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_Server_instRpcEncodableOption___redArg(v_inst_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__0(lean_object* v_inst_1171_, lean_object* v___x_1172_, lean_object* v___x_1173_, lean_object* v_a_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v_rpcEncode_1176_; size_t v_sz_1177_; size_t v___x_1178_; lean_object* v___x_648__overap_1179_; lean_object* v___x_1180_; lean_object* v_fst_1181_; lean_object* v_snd_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1190_; 
v_rpcEncode_1176_ = lean_ctor_get(v_inst_1171_, 0);
lean_inc_ref(v_rpcEncode_1176_);
lean_dec_ref(v_inst_1171_);
v_sz_1177_ = lean_array_size(v_a_1174_);
v___x_1178_ = ((size_t)0ULL);
v___x_648__overap_1179_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1172_, v_rpcEncode_1176_, v_sz_1177_, v___x_1178_, v_a_1174_);
v___x_1180_ = lean_apply_1(v___x_648__overap_1179_, v___y_1175_);
v_fst_1181_ = lean_ctor_get(v___x_1180_, 0);
v_snd_1182_ = lean_ctor_get(v___x_1180_, 1);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1184_ = v___x_1180_;
v_isShared_1185_ = v_isSharedCheck_1190_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_snd_1182_);
lean_inc(v_fst_1181_);
lean_dec(v___x_1180_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1190_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1186_ = l_Array_toJson___redArg(v___x_1173_, v_fst_1181_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1186_);
v___x_1188_ = v___x_1184_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_snd_1182_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__1(lean_object* v___f_1191_, lean_object* v_inst_1192_, lean_object* v___x_1193_, lean_object* v_b_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Array_fromJson_x3f___redArg(v___f_1191_, v_b_1194_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec_ref(v___x_1193_);
lean_dec_ref(v_inst_1192_);
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1196_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1196_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v_rpcDecode_1206_; size_t v_sz_1207_; size_t v___x_1208_; lean_object* v___x_662__overap_1209_; lean_object* v___x_1210_; 
v_a_1205_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1205_);
lean_dec_ref_known(v___x_1196_, 1);
v_rpcDecode_1206_ = lean_ctor_get(v_inst_1192_, 1);
lean_inc_ref(v_rpcDecode_1206_);
lean_dec_ref(v_inst_1192_);
v_sz_1207_ = lean_array_size(v_a_1205_);
v___x_1208_ = ((size_t)0ULL);
v___x_662__overap_1209_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1193_, v_rpcDecode_1206_, v_sz_1207_, v___x_1208_, v_a_1205_);
lean_inc_ref(v___y_1195_);
v___x_1210_ = lean_apply_1(v___x_662__overap_1209_, v___y_1195_);
return v___x_1210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__1___boxed(lean_object* v___f_1211_, lean_object* v_inst_1212_, lean_object* v___x_1213_, lean_object* v_b_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_Server_instRpcEncodableArray___redArg___lam__1(v___f_1211_, v_inst_1212_, v___x_1213_, v_b_1214_, v___y_1215_);
lean_dec_ref(v___y_1215_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg(lean_object* v_inst_1243_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___f_1246_; lean_object* v___x_1247_; lean_object* v___f_1248_; lean_object* v___f_1249_; lean_object* v___x_1250_; 
v___x_1244_ = ((lean_object*)(l_Lean_Server_instRpcEncodableArray___redArg___closed__9));
v___x_1245_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__0));
lean_inc_ref(v_inst_1243_);
v___f_1246_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableArray___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1246_, 0, v_inst_1243_);
lean_closure_set(v___f_1246_, 1, v___x_1244_);
lean_closure_set(v___f_1246_, 2, v___x_1245_);
v___x_1247_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20);
v___f_1248_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__1));
v___f_1249_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableArray___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1249_, 0, v___f_1248_);
lean_closure_set(v___f_1249_, 1, v_inst_1243_);
lean_closure_set(v___f_1249_, 2, v___x_1247_);
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___f_1246_);
lean_ctor_set(v___x_1250_, 1, v___f_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray(lean_object* v_00_u03b1_1251_, lean_object* v_inst_1252_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_Server_instRpcEncodableArray___redArg(v_inst_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg___lam__0(lean_object* v_inst_1254_, lean_object* v_inst_1255_, lean_object* v___x_1256_, lean_object* v_x_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_fst_1259_; lean_object* v_snd_1260_; lean_object* v_rpcEncode_1261_; lean_object* v___x_1262_; lean_object* v_fst_1263_; lean_object* v_snd_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1283_; 
v_fst_1259_ = lean_ctor_get(v_x_1257_, 0);
lean_inc(v_fst_1259_);
v_snd_1260_ = lean_ctor_get(v_x_1257_, 1);
lean_inc(v_snd_1260_);
lean_dec_ref(v_x_1257_);
v_rpcEncode_1261_ = lean_ctor_get(v_inst_1254_, 0);
lean_inc_ref(v_rpcEncode_1261_);
lean_dec_ref(v_inst_1254_);
v___x_1262_ = lean_apply_2(v_rpcEncode_1261_, v_fst_1259_, v___y_1258_);
v_fst_1263_ = lean_ctor_get(v___x_1262_, 0);
v_snd_1264_ = lean_ctor_get(v___x_1262_, 1);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1266_ = v___x_1262_;
v_isShared_1267_ = v_isSharedCheck_1283_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_snd_1264_);
lean_inc(v_fst_1263_);
lean_dec(v___x_1262_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1283_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v_rpcEncode_1268_; lean_object* v___x_1269_; lean_object* v_fst_1270_; lean_object* v_snd_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1282_; 
v_rpcEncode_1268_ = lean_ctor_get(v_inst_1255_, 0);
lean_inc_ref(v_rpcEncode_1268_);
lean_dec_ref(v_inst_1255_);
v___x_1269_ = lean_apply_2(v_rpcEncode_1268_, v_snd_1260_, v_snd_1264_);
v_fst_1270_ = lean_ctor_get(v___x_1269_, 0);
v_snd_1271_ = lean_ctor_get(v___x_1269_, 1);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1273_ = v___x_1269_;
v_isShared_1274_ = v_isSharedCheck_1282_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_snd_1271_);
lean_inc(v_fst_1270_);
lean_dec(v___x_1269_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1282_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 1, v_fst_1270_);
lean_ctor_set(v___x_1273_, 0, v_fst_1263_);
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_fst_1263_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_fst_1270_);
v___x_1276_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1277_; lean_object* v___x_1279_; 
lean_inc_ref(v___x_1256_);
v___x_1277_ = l_Prod_toJson___redArg(v___x_1256_, v___x_1256_, v___x_1276_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v_snd_1271_);
lean_ctor_set(v___x_1266_, 0, v___x_1277_);
v___x_1279_ = v___x_1266_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1277_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_snd_1271_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg___lam__1(lean_object* v___f_1284_, lean_object* v_inst_1285_, lean_object* v_inst_1286_, lean_object* v_j_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___x_1289_; 
lean_inc_ref(v___f_1284_);
v___x_1289_ = l_Prod_fromJson_x3f___redArg(v___f_1284_, v___f_1284_, v_j_1287_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec_ref(v_inst_1286_);
lean_dec_ref(v_inst_1285_);
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1289_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v_fst_1299_; lean_object* v_snd_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1336_; 
v_a_1298_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1289_, 1);
v_fst_1299_ = lean_ctor_get(v_a_1298_, 0);
v_snd_1300_ = lean_ctor_get(v_a_1298_, 1);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_a_1298_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1302_ = v_a_1298_;
v_isShared_1303_ = v_isSharedCheck_1336_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_snd_1300_);
lean_inc(v_fst_1299_);
lean_dec(v_a_1298_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1336_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v_rpcDecode_1304_; lean_object* v___x_1305_; 
v_rpcDecode_1304_ = lean_ctor_get(v_inst_1285_, 1);
lean_inc_ref(v_rpcDecode_1304_);
lean_dec_ref(v_inst_1285_);
lean_inc_ref(v___y_1288_);
v___x_1305_ = lean_apply_2(v_rpcDecode_1304_, v_fst_1299_, v___y_1288_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_del_object(v___x_1302_);
lean_dec(v_snd_1300_);
lean_dec_ref(v_inst_1286_);
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
lean_object* v_a_1314_; lean_object* v_rpcDecode_1315_; lean_object* v___x_1316_; 
v_a_1314_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1314_);
lean_dec_ref_known(v___x_1305_, 1);
v_rpcDecode_1315_ = lean_ctor_get(v_inst_1286_, 1);
lean_inc_ref(v_rpcDecode_1315_);
lean_dec_ref(v_inst_1286_);
lean_inc_ref(v___y_1288_);
v___x_1316_ = lean_apply_2(v_rpcDecode_1315_, v_snd_1300_, v___y_1288_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec(v_a_1314_);
lean_del_object(v___x_1302_);
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
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1335_; 
v_a_1325_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1327_ = v___x_1316_;
v_isShared_1328_ = v_isSharedCheck_1335_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1316_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1335_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 1, v_a_1325_);
lean_ctor_set(v___x_1302_, 0, v_a_1314_);
v___x_1330_ = v___x_1302_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1314_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1332_; 
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v___x_1330_);
v___x_1332_ = v___x_1327_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg___lam__1___boxed(lean_object* v___f_1337_, lean_object* v_inst_1338_, lean_object* v_inst_1339_, lean_object* v_j_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_Server_instRpcEncodableProd___redArg___lam__1(v___f_1337_, v_inst_1338_, v_inst_1339_, v_j_1340_, v___y_1341_);
lean_dec_ref(v___y_1341_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg(lean_object* v_inst_1343_, lean_object* v_inst_1344_){
_start:
{
lean_object* v___x_1345_; lean_object* v___f_1346_; lean_object* v___f_1347_; lean_object* v___f_1348_; lean_object* v___x_1349_; 
v___x_1345_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__0));
lean_inc_ref(v_inst_1344_);
lean_inc_ref(v_inst_1343_);
v___f_1346_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableProd___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1346_, 0, v_inst_1343_);
lean_closure_set(v___f_1346_, 1, v_inst_1344_);
lean_closure_set(v___f_1346_, 2, v___x_1345_);
v___f_1347_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__1));
v___f_1348_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableProd___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1348_, 0, v___f_1347_);
lean_closure_set(v___f_1348_, 1, v_inst_1343_);
lean_closure_set(v___f_1348_, 2, v_inst_1344_);
v___x_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___f_1346_);
lean_ctor_set(v___x_1349_, 1, v___f_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd(lean_object* v_00_u03b1_1350_, lean_object* v_00_u03b2_1351_, lean_object* v_inst_1352_, lean_object* v_inst_1353_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_Server_instRpcEncodableProd___redArg(v_inst_1352_, v_inst_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__0(lean_object* v_inst_1355_, lean_object* v_fn_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_rpcEncode_1358_; lean_object* v___x_1359_; lean_object* v_fst_1360_; lean_object* v_snd_1361_; lean_object* v___x_1362_; 
v_rpcEncode_1358_ = lean_ctor_get(v_inst_1355_, 0);
lean_inc_ref(v_rpcEncode_1358_);
lean_dec_ref(v_inst_1355_);
v___x_1359_ = lean_apply_1(v_fn_1356_, v___y_1357_);
v_fst_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_fst_1360_);
v_snd_1361_ = lean_ctor_get(v___x_1359_, 1);
lean_inc(v_snd_1361_);
lean_dec_ref(v___x_1359_);
v___x_1362_ = lean_apply_2(v_rpcEncode_1358_, v_fst_1360_, v_snd_1361_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1(lean_object* v_inst_1363_, lean_object* v___x_1364_, lean_object* v_j_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_rpcDecode_1367_; lean_object* v___x_1368_; 
v_rpcDecode_1367_ = lean_ctor_get(v_inst_1363_, 1);
lean_inc_ref(v_rpcDecode_1367_);
lean_dec_ref(v_inst_1363_);
lean_inc_ref(v___y_1366_);
v___x_1368_ = lean_apply_2(v_rpcDecode_1367_, v_j_1365_, v___y_1366_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec_ref(v___x_1364_);
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1385_; 
v_a_1377_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1379_ = v___x_1368_;
v_isShared_1380_ = v_isSharedCheck_1385_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1368_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1385_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; lean_object* v___x_1383_; 
v___x_1381_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 5);
lean_closure_set(v___x_1381_, 0, lean_box(0));
lean_closure_set(v___x_1381_, 1, lean_box(0));
lean_closure_set(v___x_1381_, 2, v___x_1364_);
lean_closure_set(v___x_1381_, 3, lean_box(0));
lean_closure_set(v___x_1381_, 4, v_a_1377_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1381_);
v___x_1383_ = v___x_1379_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1___boxed(lean_object* v_inst_1386_, lean_object* v___x_1387_, lean_object* v_j_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1(v_inst_1386_, v___x_1387_, v_j_1388_, v___y_1389_);
lean_dec_ref(v___y_1389_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg(lean_object* v_inst_1391_){
_start:
{
lean_object* v___f_1392_; lean_object* v___x_1393_; lean_object* v___f_1394_; lean_object* v___x_1395_; 
lean_inc_ref(v_inst_1391_);
v___f_1392_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1392_, 0, v_inst_1391_);
v___x_1393_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9));
v___f_1394_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1394_, 0, v_inst_1391_);
lean_closure_set(v___f_1394_, 1, v___x_1393_);
v___x_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___f_1392_);
lean_ctor_set(v___x_1395_, 1, v___f_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore(lean_object* v_00_u03b1_1396_, lean_object* v_inst_1397_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg(v_inst_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(lean_object* v_inst_1399_, lean_object* v_r_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v___x_1402_; lean_object* v_fst_1403_; lean_object* v_snd_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1423_; 
v___x_1402_ = l_Lean_Server_rpcStoreRef___redArg(v_inst_1399_, v_r_1400_, v_a_1401_);
v_fst_1403_ = lean_ctor_get(v___x_1402_, 0);
v_snd_1404_ = lean_ctor_get(v___x_1402_, 1);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1406_ = v___x_1402_;
v_isShared_1407_ = v_isSharedCheck_1423_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_snd_1404_);
lean_inc(v_fst_1403_);
lean_dec(v___x_1402_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1423_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___y_1409_; uint8_t v_wireFormat_1420_; 
v_wireFormat_1420_ = lean_ctor_get_uint8(v_snd_1404_, sizeof(void*)*3);
if (v_wireFormat_1420_ == 0)
{
lean_object* v___x_1421_; 
v___x_1421_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0));
v___y_1409_ = v___x_1421_;
goto v___jp_1408_;
}
else
{
lean_object* v___x_1422_; 
v___x_1422_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1));
v___y_1409_ = v___x_1422_;
goto v___jp_1408_;
}
v___jp_1408_:
{
size_t v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1410_ = lean_unbox_usize(v_fst_1403_);
lean_dec(v_fst_1403_);
v___x_1411_ = lean_usize_to_nat(v___x_1410_);
v___x_1412_ = l_Lean_bignumToJson(v___x_1411_);
lean_inc_ref(v___y_1409_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 1, v___x_1412_);
lean_ctor_set(v___x_1406_, 0, v___y_1409_);
v___x_1414_ = v___x_1406_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___y_1409_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1415_ = lean_box(0);
v___x_1416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1414_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = l_Lean_Json_mkObj(v___x_1416_);
lean_dec_ref_known(v___x_1416_, 2);
v___x_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
lean_ctor_set(v___x_1418_, 1, v_snd_1404_);
return v___x_1418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg___boxed(lean_object* v_inst_1424_, lean_object* v_r_1425_, lean_object* v_a_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(v_inst_1424_, v_r_1425_, v_a_1426_);
lean_dec_ref(v_r_1425_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode(lean_object* v_00_u03b1_1428_, lean_object* v_inst_1429_, lean_object* v_r_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(v_inst_1429_, v_r_1430_, v_a_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___boxed(lean_object* v_00_u03b1_1433_, lean_object* v_inst_1434_, lean_object* v_r_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode(v_00_u03b1_1433_, v_inst_1434_, v_r_1435_, v_a_1436_);
lean_dec_ref(v_r_1435_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(lean_object* v_inst_1439_, lean_object* v_j_1440_, lean_object* v_a_1441_){
_start:
{
uint8_t v_wireFormat_1442_; lean_object* v___x_1443_; lean_object* v___y_1445_; 
v_wireFormat_1442_ = lean_ctor_get_uint8(v_a_1441_, sizeof(void*)*3);
v___x_1443_ = ((lean_object*)(l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg___closed__0));
if (v_wireFormat_1442_ == 0)
{
lean_object* v___x_1458_; 
v___x_1458_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0));
v___y_1445_ = v___x_1458_;
goto v___jp_1444_;
}
else
{
lean_object* v___x_1459_; 
v___x_1459_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1));
v___y_1445_ = v___x_1459_;
goto v___jp_1444_;
}
v___jp_1444_:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1440_, v___x_1443_, v___y_1445_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec(v_inst_1439_);
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1446_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1446_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
else
{
lean_object* v_a_1455_; size_t v___x_1456_; lean_object* v___x_1457_; 
v_a_1455_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1455_);
lean_dec_ref_known(v___x_1446_, 1);
v___x_1456_ = lean_unbox_usize(v_a_1455_);
lean_dec(v_a_1455_);
v___x_1457_ = l_Lean_Server_rpcGetRef___redArg(v_inst_1439_, v___x_1456_, v_a_1441_);
return v___x_1457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg___boxed(lean_object* v_inst_1460_, lean_object* v_j_1461_, lean_object* v_a_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v_inst_1460_, v_j_1461_, v_a_1462_);
lean_dec_ref(v_a_1462_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode(lean_object* v_00_u03b1_1464_, lean_object* v_inst_1465_, lean_object* v_j_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v_inst_1465_, v_j_1466_, v_a_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___boxed(lean_object* v_00_u03b1_1469_, lean_object* v_inst_1470_, lean_object* v_j_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode(v_00_u03b1_1469_, v_inst_1470_, v_j_1471_, v_a_1472_);
lean_dec_ref(v_a_1472_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName___redArg(lean_object* v_inst_1474_){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
lean_inc(v_inst_1474_);
v___x_1475_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___boxed), 4, 2);
lean_closure_set(v___x_1475_, 0, lean_box(0));
lean_closure_set(v___x_1475_, 1, v_inst_1474_);
v___x_1476_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___boxed), 4, 2);
lean_closure_set(v___x_1476_, 0, lean_box(0));
lean_closure_set(v___x_1476_, 1, v_inst_1474_);
v___x_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1475_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName(lean_object* v_00_u03b1_1478_, lean_object* v_inst_1479_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName___redArg(v_inst_1479_);
return v___x_1480_;
}
}
lean_object* runtime_initialize_Init_Dynamic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Rpc_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
