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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1;
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
lean_dec_ref(v___x_101_);
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
lean_inc_ref(v_refsById_192_);
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
lean_dec_ref(v___x_202_);
lean_inc_ref(v_aliveRefs_191_);
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
lean_dec_ref(v___x_225_);
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
lean_inc_ref(v_aliveRefs_278_);
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
static size_t _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_370_; size_t v___x_371_; size_t v___x_372_; 
v___x_370_ = ((size_t)5ULL);
v___x_371_ = ((size_t)1ULL);
v___x_372_ = lean_usize_shift_left(v___x_371_, v___x_370_);
return v___x_372_;
}
}
static size_t _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_373_; size_t v___x_374_; size_t v___x_375_; 
v___x_373_ = ((size_t)1ULL);
v___x_374_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__0);
v___x_375_ = lean_usize_sub(v___x_374_, v___x_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(lean_object* v_x_376_, size_t v_x_377_, size_t v_x_378_){
_start:
{
if (lean_obj_tag(v_x_376_) == 0)
{
lean_object* v_es_379_; lean_object* v___x_380_; size_t v___x_381_; size_t v___x_382_; size_t v___x_383_; lean_object* v_j_384_; lean_object* v_entry_385_; 
v_es_379_ = lean_ctor_get(v_x_376_, 0);
v___x_380_ = lean_box(2);
v___x_381_ = ((size_t)5ULL);
v___x_382_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1);
v___x_383_ = lean_usize_land(v_x_377_, v___x_382_);
v_j_384_ = lean_usize_to_nat(v___x_383_);
v_entry_385_ = lean_array_get(v___x_380_, v_es_379_, v_j_384_);
switch(lean_obj_tag(v_entry_385_))
{
case 0:
{
lean_object* v_key_386_; size_t v___x_387_; uint8_t v___x_388_; 
v_key_386_ = lean_ctor_get(v_entry_385_, 0);
lean_inc(v_key_386_);
lean_dec_ref(v_entry_385_);
v___x_387_ = lean_unbox_usize(v_key_386_);
lean_dec(v_key_386_);
v___x_388_ = lean_usize_dec_eq(v_x_378_, v___x_387_);
if (v___x_388_ == 0)
{
lean_dec(v_j_384_);
return v_x_376_;
}
else
{
lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_396_; 
lean_inc_ref(v_es_379_);
v_isSharedCheck_396_ = !lean_is_exclusive(v_x_376_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; 
v_unused_397_ = lean_ctor_get(v_x_376_, 0);
lean_dec(v_unused_397_);
v___x_390_ = v_x_376_;
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
else
{
lean_dec(v_x_376_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_392_ = lean_array_set(v_es_379_, v_j_384_, v___x_380_);
lean_dec(v_j_384_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_392_);
v___x_394_ = v___x_390_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
case 1:
{
lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_431_; 
lean_inc_ref(v_es_379_);
v_isSharedCheck_431_ = !lean_is_exclusive(v_x_376_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; 
v_unused_432_ = lean_ctor_get(v_x_376_, 0);
lean_dec(v_unused_432_);
v___x_399_ = v_x_376_;
v_isShared_400_ = v_isSharedCheck_431_;
goto v_resetjp_398_;
}
else
{
lean_dec(v_x_376_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_431_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v_node_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_430_; 
v_node_401_ = lean_ctor_get(v_entry_385_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v_entry_385_);
if (v_isSharedCheck_430_ == 0)
{
v___x_403_ = v_entry_385_;
v_isShared_404_ = v_isSharedCheck_430_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_node_401_);
lean_dec(v_entry_385_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_430_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v_entries_405_; size_t v___x_406_; lean_object* v_newNode_407_; lean_object* v___x_408_; 
v_entries_405_ = lean_array_set(v_es_379_, v_j_384_, v___x_380_);
v___x_406_ = lean_usize_shift_right(v_x_377_, v___x_381_);
v_newNode_407_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_node_401_, v___x_406_, v_x_378_);
lean_inc_ref(v_newNode_407_);
v___x_408_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_407_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v___x_410_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v_newNode_407_);
v___x_410_ = v___x_403_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_newNode_407_);
v___x_410_ = v_reuseFailAlloc_415_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_411_ = lean_array_set(v_entries_405_, v_j_384_, v___x_410_);
lean_dec(v_j_384_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_411_);
v___x_413_ = v___x_399_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
else
{
lean_object* v_val_416_; lean_object* v_fst_417_; lean_object* v_snd_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_429_; 
lean_dec_ref(v_newNode_407_);
lean_del_object(v___x_403_);
v_val_416_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_val_416_);
lean_dec_ref(v___x_408_);
v_fst_417_ = lean_ctor_get(v_val_416_, 0);
v_snd_418_ = lean_ctor_get(v_val_416_, 1);
v_isSharedCheck_429_ = !lean_is_exclusive(v_val_416_);
if (v_isSharedCheck_429_ == 0)
{
v___x_420_ = v_val_416_;
v_isShared_421_ = v_isSharedCheck_429_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_snd_418_);
lean_inc(v_fst_417_);
lean_dec(v_val_416_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_429_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_fst_417_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_snd_418_);
v___x_423_ = v_reuseFailAlloc_428_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_424_; lean_object* v___x_426_; 
v___x_424_ = lean_array_set(v_entries_405_, v_j_384_, v___x_423_);
lean_dec(v_j_384_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_424_);
v___x_426_ = v___x_399_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_384_);
return v_x_376_;
}
}
}
else
{
lean_object* v_ks_433_; lean_object* v_vs_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_448_; 
v_ks_433_ = lean_ctor_get(v_x_376_, 0);
v_vs_434_ = lean_ctor_get(v_x_376_, 1);
v_isSharedCheck_448_ = !lean_is_exclusive(v_x_376_);
if (v_isSharedCheck_448_ == 0)
{
v___x_436_ = v_x_376_;
v_isShared_437_ = v_isSharedCheck_448_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_vs_434_);
lean_inc(v_ks_433_);
lean_dec(v_x_376_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_448_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; 
v___x_438_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8(v_ks_433_, v_x_378_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v___x_440_; 
if (v_isShared_437_ == 0)
{
v___x_440_ = v___x_436_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_ks_433_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_vs_434_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
else
{
lean_object* v_val_442_; lean_object* v_keys_x27_443_; lean_object* v_vals_x27_444_; lean_object* v___x_446_; 
v_val_442_ = lean_ctor_get(v___x_438_, 0);
lean_inc_n(v_val_442_, 2);
lean_dec_ref(v___x_438_);
v_keys_x27_443_ = l_Array_eraseIdx___redArg(v_ks_433_, v_val_442_);
v_vals_x27_444_ = l_Array_eraseIdx___redArg(v_vs_434_, v_val_442_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 1, v_vals_x27_444_);
lean_ctor_set(v___x_436_, 0, v_keys_x27_443_);
v___x_446_ = v___x_436_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_keys_x27_443_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_vals_x27_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___boxed(lean_object* v_x_449_, lean_object* v_x_450_, lean_object* v_x_451_){
_start:
{
size_t v_x_1722__boxed_452_; size_t v_x_1723__boxed_453_; lean_object* v_res_454_; 
v_x_1722__boxed_452_ = lean_unbox_usize(v_x_450_);
lean_dec(v_x_450_);
v_x_1723__boxed_453_ = lean_unbox_usize(v_x_451_);
lean_dec(v_x_451_);
v_res_454_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_x_449_, v_x_1722__boxed_452_, v_x_1723__boxed_453_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(lean_object* v_x_455_, size_t v_x_456_){
_start:
{
uint64_t v___x_457_; size_t v_h_458_; lean_object* v___x_459_; 
v___x_457_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_456_);
v_h_458_ = lean_uint64_to_usize(v___x_457_);
v___x_459_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_x_455_, v_h_458_, v_x_456_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg___boxed(lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
size_t v_x_1866__boxed_462_; lean_object* v_res_463_; 
v_x_1866__boxed_462_ = lean_unbox_usize(v_x_461_);
lean_dec(v_x_461_);
v_res_463_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(v_x_460_, v_x_1866__boxed_462_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_464_, lean_object* v_vals_465_, lean_object* v_i_466_, size_t v_k_467_){
_start:
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = lean_array_get_size(v_keys_464_);
v___x_469_ = lean_nat_dec_lt(v_i_466_, v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; 
lean_dec(v_i_466_);
v___x_470_ = lean_box(0);
return v___x_470_;
}
else
{
lean_object* v_k_x27_471_; size_t v___x_472_; uint8_t v___x_473_; 
v_k_x27_471_ = lean_array_fget_borrowed(v_keys_464_, v_i_466_);
v___x_472_ = lean_unbox_usize(v_k_x27_471_);
v___x_473_ = lean_usize_dec_eq(v_k_467_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = lean_unsigned_to_nat(1u);
v___x_475_ = lean_nat_add(v_i_466_, v___x_474_);
lean_dec(v_i_466_);
v_i_466_ = v___x_475_;
goto _start;
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_array_fget_borrowed(v_vals_465_, v_i_466_);
lean_dec(v_i_466_);
lean_inc(v___x_477_);
v___x_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_479_, lean_object* v_vals_480_, lean_object* v_i_481_, lean_object* v_k_482_){
_start:
{
size_t v_k_boxed_483_; lean_object* v_res_484_; 
v_k_boxed_483_ = lean_unbox_usize(v_k_482_);
lean_dec(v_k_482_);
v_res_484_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(v_keys_479_, v_vals_480_, v_i_481_, v_k_boxed_483_);
lean_dec_ref(v_vals_480_);
lean_dec_ref(v_keys_479_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(lean_object* v_x_485_, size_t v_x_486_, size_t v_x_487_){
_start:
{
if (lean_obj_tag(v_x_485_) == 0)
{
lean_object* v_es_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_510_; 
v_es_488_ = lean_ctor_get(v_x_485_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v_x_485_);
if (v_isSharedCheck_510_ == 0)
{
v___x_490_ = v_x_485_;
v_isShared_491_ = v_isSharedCheck_510_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_es_488_);
lean_dec(v_x_485_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_510_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; size_t v___x_493_; size_t v___x_494_; size_t v___x_495_; lean_object* v_j_496_; lean_object* v___x_497_; 
v___x_492_ = lean_box(2);
v___x_493_ = ((size_t)5ULL);
v___x_494_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1);
v___x_495_ = lean_usize_land(v_x_486_, v___x_494_);
v_j_496_ = lean_usize_to_nat(v___x_495_);
v___x_497_ = lean_array_get(v___x_492_, v_es_488_, v_j_496_);
lean_dec(v_j_496_);
lean_dec_ref(v_es_488_);
switch(lean_obj_tag(v___x_497_))
{
case 0:
{
lean_object* v_key_498_; lean_object* v_val_499_; size_t v___x_500_; uint8_t v___x_501_; 
v_key_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_key_498_);
v_val_499_ = lean_ctor_get(v___x_497_, 1);
lean_inc(v_val_499_);
lean_dec_ref(v___x_497_);
v___x_500_ = lean_unbox_usize(v_key_498_);
lean_dec(v_key_498_);
v___x_501_ = lean_usize_dec_eq(v_x_487_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
lean_dec(v_val_499_);
lean_del_object(v___x_490_);
v___x_502_ = lean_box(0);
return v___x_502_;
}
else
{
lean_object* v___x_504_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set_tag(v___x_490_, 1);
lean_ctor_set(v___x_490_, 0, v_val_499_);
v___x_504_ = v___x_490_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_val_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
case 1:
{
lean_object* v_node_506_; size_t v___x_507_; 
lean_del_object(v___x_490_);
v_node_506_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_node_506_);
lean_dec_ref(v___x_497_);
v___x_507_ = lean_usize_shift_right(v_x_486_, v___x_493_);
v_x_485_ = v_node_506_;
v_x_486_ = v___x_507_;
goto _start;
}
default: 
{
lean_object* v___x_509_; 
lean_del_object(v___x_490_);
v___x_509_ = lean_box(0);
return v___x_509_;
}
}
}
}
else
{
lean_object* v_ks_511_; lean_object* v_vs_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_ks_511_ = lean_ctor_get(v_x_485_, 0);
lean_inc_ref(v_ks_511_);
v_vs_512_ = lean_ctor_get(v_x_485_, 1);
lean_inc_ref(v_vs_512_);
lean_dec_ref(v_x_485_);
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(v_ks_511_, v_vs_512_, v___x_513_, v_x_487_);
lean_dec_ref(v_vs_512_);
lean_dec_ref(v_ks_511_);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg___boxed(lean_object* v_x_515_, lean_object* v_x_516_, lean_object* v_x_517_){
_start:
{
size_t v_x_1902__boxed_518_; size_t v_x_1903__boxed_519_; lean_object* v_res_520_; 
v_x_1902__boxed_518_ = lean_unbox_usize(v_x_516_);
lean_dec(v_x_516_);
v_x_1903__boxed_519_ = lean_unbox_usize(v_x_517_);
lean_dec(v_x_517_);
v_res_520_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_515_, v_x_1902__boxed_518_, v_x_1903__boxed_519_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(lean_object* v_x_521_, size_t v_x_522_){
_start:
{
uint64_t v___x_523_; size_t v___x_524_; lean_object* v___x_525_; 
v___x_523_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_522_);
v___x_524_ = lean_uint64_to_usize(v___x_523_);
v___x_525_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_521_, v___x_524_, v_x_522_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg___boxed(lean_object* v_x_526_, lean_object* v_x_527_){
_start:
{
size_t v_x_1965__boxed_528_; lean_object* v_res_529_; 
v_x_1965__boxed_528_ = lean_unbox_usize(v_x_527_);
lean_dec(v_x_527_);
v_res_529_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(v_x_526_, v_x_1965__boxed_528_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(lean_object* v_xs_530_, size_t v_v_531_, lean_object* v_i_532_){
_start:
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = lean_array_get_size(v_xs_530_);
v___x_534_ = lean_nat_dec_lt(v_i_532_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; 
lean_dec(v_i_532_);
v___x_535_ = lean_box(0);
return v___x_535_;
}
else
{
lean_object* v___x_536_; size_t v___x_537_; uint8_t v___x_538_; 
v___x_536_ = lean_array_fget_borrowed(v_xs_530_, v_i_532_);
v___x_537_ = lean_unbox_usize(v___x_536_);
v___x_538_ = lean_usize_dec_eq(v___x_537_, v_v_531_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_unsigned_to_nat(1u);
v___x_540_ = lean_nat_add(v_i_532_, v___x_539_);
lean_dec(v_i_532_);
v_i_532_ = v___x_540_;
goto _start;
}
else
{
lean_object* v___x_542_; 
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v_i_532_);
return v___x_542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14___boxed(lean_object* v_xs_543_, lean_object* v_v_544_, lean_object* v_i_545_){
_start:
{
size_t v_v_boxed_546_; lean_object* v_res_547_; 
v_v_boxed_546_ = lean_unbox_usize(v_v_544_);
lean_dec(v_v_544_);
v_res_547_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(v_xs_543_, v_v_boxed_546_, v_i_545_);
lean_dec_ref(v_xs_543_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(lean_object* v_xs_548_, size_t v_v_549_){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(v_xs_548_, v_v_549_, v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11___boxed(lean_object* v_xs_552_, lean_object* v_v_553_){
_start:
{
size_t v_v_boxed_554_; lean_object* v_res_555_; 
v_v_boxed_554_ = lean_unbox_usize(v_v_553_);
lean_dec(v_v_553_);
v_res_555_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(v_xs_552_, v_v_boxed_554_);
lean_dec_ref(v_xs_552_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(lean_object* v_x_556_, size_t v_x_557_, size_t v_x_558_){
_start:
{
if (lean_obj_tag(v_x_556_) == 0)
{
lean_object* v_es_559_; lean_object* v___x_560_; size_t v___x_561_; size_t v___x_562_; size_t v___x_563_; lean_object* v_j_564_; lean_object* v_entry_565_; 
v_es_559_ = lean_ctor_get(v_x_556_, 0);
v___x_560_ = lean_box(2);
v___x_561_ = ((size_t)5ULL);
v___x_562_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1);
v___x_563_ = lean_usize_land(v_x_557_, v___x_562_);
v_j_564_ = lean_usize_to_nat(v___x_563_);
v_entry_565_ = lean_array_get(v___x_560_, v_es_559_, v_j_564_);
switch(lean_obj_tag(v_entry_565_))
{
case 0:
{
lean_object* v_key_566_; size_t v___x_567_; uint8_t v___x_568_; 
v_key_566_ = lean_ctor_get(v_entry_565_, 0);
lean_inc(v_key_566_);
lean_dec_ref(v_entry_565_);
v___x_567_ = lean_unbox_usize(v_key_566_);
lean_dec(v_key_566_);
v___x_568_ = lean_usize_dec_eq(v_x_558_, v___x_567_);
if (v___x_568_ == 0)
{
lean_dec(v_j_564_);
return v_x_556_;
}
else
{
lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_576_; 
lean_inc_ref(v_es_559_);
v_isSharedCheck_576_ = !lean_is_exclusive(v_x_556_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; 
v_unused_577_ = lean_ctor_get(v_x_556_, 0);
lean_dec(v_unused_577_);
v___x_570_ = v_x_556_;
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
else
{
lean_dec(v_x_556_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_572_ = lean_array_set(v_es_559_, v_j_564_, v___x_560_);
lean_dec(v_j_564_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_572_);
v___x_574_ = v___x_570_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
case 1:
{
lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_611_; 
lean_inc_ref(v_es_559_);
v_isSharedCheck_611_ = !lean_is_exclusive(v_x_556_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; 
v_unused_612_ = lean_ctor_get(v_x_556_, 0);
lean_dec(v_unused_612_);
v___x_579_ = v_x_556_;
v_isShared_580_ = v_isSharedCheck_611_;
goto v_resetjp_578_;
}
else
{
lean_dec(v_x_556_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_611_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v_node_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_610_; 
v_node_581_ = lean_ctor_get(v_entry_565_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v_entry_565_);
if (v_isSharedCheck_610_ == 0)
{
v___x_583_ = v_entry_565_;
v_isShared_584_ = v_isSharedCheck_610_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_node_581_);
lean_dec(v_entry_565_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_610_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v_entries_585_; size_t v___x_586_; lean_object* v_newNode_587_; lean_object* v___x_588_; 
v_entries_585_ = lean_array_set(v_es_559_, v_j_564_, v___x_560_);
v___x_586_ = lean_usize_shift_right(v_x_557_, v___x_561_);
v_newNode_587_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_node_581_, v___x_586_, v_x_558_);
lean_inc_ref(v_newNode_587_);
v___x_588_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_587_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v___x_590_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v_newNode_587_);
v___x_590_ = v___x_583_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_newNode_587_);
v___x_590_ = v_reuseFailAlloc_595_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_591_ = lean_array_set(v_entries_585_, v_j_564_, v___x_590_);
lean_dec(v_j_564_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_591_);
v___x_593_ = v___x_579_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
else
{
lean_object* v_val_596_; lean_object* v_fst_597_; lean_object* v_snd_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_609_; 
lean_dec_ref(v_newNode_587_);
lean_del_object(v___x_583_);
v_val_596_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_val_596_);
lean_dec_ref(v___x_588_);
v_fst_597_ = lean_ctor_get(v_val_596_, 0);
v_snd_598_ = lean_ctor_get(v_val_596_, 1);
v_isSharedCheck_609_ = !lean_is_exclusive(v_val_596_);
if (v_isSharedCheck_609_ == 0)
{
v___x_600_ = v_val_596_;
v_isShared_601_ = v_isSharedCheck_609_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_snd_598_);
lean_inc(v_fst_597_);
lean_dec(v_val_596_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_609_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_fst_597_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_snd_598_);
v___x_603_ = v_reuseFailAlloc_608_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_604_ = lean_array_set(v_entries_585_, v_j_564_, v___x_603_);
lean_dec(v_j_564_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_604_);
v___x_606_ = v___x_579_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_564_);
return v_x_556_;
}
}
}
else
{
lean_object* v_ks_613_; lean_object* v_vs_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_628_; 
v_ks_613_ = lean_ctor_get(v_x_556_, 0);
v_vs_614_ = lean_ctor_get(v_x_556_, 1);
v_isSharedCheck_628_ = !lean_is_exclusive(v_x_556_);
if (v_isSharedCheck_628_ == 0)
{
v___x_616_ = v_x_556_;
v_isShared_617_ = v_isSharedCheck_628_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_vs_614_);
lean_inc(v_ks_613_);
lean_dec(v_x_556_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_628_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; 
v___x_618_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(v_ks_613_, v_x_558_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v___x_620_; 
if (v_isShared_617_ == 0)
{
v___x_620_ = v___x_616_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_ks_613_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_vs_614_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
else
{
lean_object* v_val_622_; lean_object* v_keys_x27_623_; lean_object* v_vals_x27_624_; lean_object* v___x_626_; 
v_val_622_ = lean_ctor_get(v___x_618_, 0);
lean_inc_n(v_val_622_, 2);
lean_dec_ref(v___x_618_);
v_keys_x27_623_ = l_Array_eraseIdx___redArg(v_ks_613_, v_val_622_);
v_vals_x27_624_ = l_Array_eraseIdx___redArg(v_vs_614_, v_val_622_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 1, v_vals_x27_624_);
lean_ctor_set(v___x_616_, 0, v_keys_x27_623_);
v___x_626_ = v___x_616_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_keys_x27_623_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_vals_x27_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg___boxed(lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
size_t v_x_2007__boxed_632_; size_t v_x_2008__boxed_633_; lean_object* v_res_634_; 
v_x_2007__boxed_632_ = lean_unbox_usize(v_x_630_);
lean_dec(v_x_630_);
v_x_2008__boxed_633_ = lean_unbox_usize(v_x_631_);
lean_dec(v_x_631_);
v_res_634_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_629_, v_x_2007__boxed_632_, v_x_2008__boxed_633_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(lean_object* v_x_635_, size_t v_x_636_){
_start:
{
uint64_t v___x_637_; size_t v_h_638_; lean_object* v___x_639_; 
v___x_637_ = lean_usize_to_uint64(v_x_636_);
v_h_638_ = lean_uint64_to_usize(v___x_637_);
v___x_639_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_635_, v_h_638_, v_x_636_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg___boxed(lean_object* v_x_640_, lean_object* v_x_641_){
_start:
{
size_t v_x_2147__boxed_642_; lean_object* v_res_643_; 
v_x_2147__boxed_642_ = lean_unbox_usize(v_x_641_);
lean_dec(v_x_641_);
v_res_643_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(v_x_640_, v_x_2147__boxed_642_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_x_644_, lean_object* v_x_645_, size_t v_x_646_, lean_object* v_x_647_){
_start:
{
lean_object* v_ks_648_; lean_object* v_vs_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_676_; 
v_ks_648_ = lean_ctor_get(v_x_644_, 0);
v_vs_649_ = lean_ctor_get(v_x_644_, 1);
v_isSharedCheck_676_ = !lean_is_exclusive(v_x_644_);
if (v_isSharedCheck_676_ == 0)
{
v___x_651_ = v_x_644_;
v_isShared_652_ = v_isSharedCheck_676_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_vs_649_);
lean_inc(v_ks_648_);
lean_dec(v_x_644_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_676_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = lean_array_get_size(v_ks_648_);
v___x_654_ = lean_nat_dec_lt(v_x_645_, v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
lean_dec(v_x_645_);
v___x_655_ = lean_box_usize(v_x_646_);
v___x_656_ = lean_array_push(v_ks_648_, v___x_655_);
v___x_657_ = lean_array_push(v_vs_649_, v_x_647_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 1, v___x_657_);
lean_ctor_set(v___x_651_, 0, v___x_656_);
v___x_659_ = v___x_651_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
else
{
lean_object* v_k_x27_661_; size_t v___x_662_; uint8_t v___x_663_; 
v_k_x27_661_ = lean_array_fget_borrowed(v_ks_648_, v_x_645_);
v___x_662_ = lean_unbox_usize(v_k_x27_661_);
v___x_663_ = lean_usize_dec_eq(v_x_646_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_665_; 
if (v_isShared_652_ == 0)
{
v___x_665_ = v___x_651_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_ks_648_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_vs_649_);
v___x_665_ = v_reuseFailAlloc_669_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_unsigned_to_nat(1u);
v___x_667_ = lean_nat_add(v_x_645_, v___x_666_);
lean_dec(v_x_645_);
v_x_644_ = v___x_665_;
v_x_645_ = v___x_667_;
goto _start;
}
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_670_ = lean_box_usize(v_x_646_);
v___x_671_ = lean_array_fset(v_ks_648_, v_x_645_, v___x_670_);
v___x_672_ = lean_array_fset(v_vs_649_, v_x_645_, v_x_647_);
lean_dec(v_x_645_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 1, v___x_672_);
lean_ctor_set(v___x_651_, 0, v___x_671_);
v___x_674_ = v___x_651_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v___x_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_x_677_, lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
size_t v_x_2158__boxed_681_; lean_object* v_res_682_; 
v_x_2158__boxed_681_ = lean_unbox_usize(v_x_679_);
lean_dec(v_x_679_);
v_res_682_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_x_677_, v_x_678_, v_x_2158__boxed_681_, v_x_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(lean_object* v_n_683_, size_t v_k_684_, lean_object* v_v_685_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_n_683_, v___x_686_, v_k_684_, v_v_685_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_n_688_, lean_object* v_k_689_, lean_object* v_v_690_){
_start:
{
size_t v_k_boxed_691_; lean_object* v_res_692_; 
v_k_boxed_691_ = lean_unbox_usize(v_k_689_);
lean_dec(v_k_689_);
v_res_692_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v_n_688_, v_k_boxed_691_, v_v_690_);
return v_res_692_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(lean_object* v_x_694_, size_t v_x_695_, size_t v_x_696_, size_t v_x_697_, lean_object* v_x_698_){
_start:
{
if (lean_obj_tag(v_x_694_) == 0)
{
lean_object* v_es_699_; size_t v___x_700_; size_t v___x_701_; size_t v___x_702_; size_t v___x_703_; lean_object* v_j_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v_es_699_ = lean_ctor_get(v_x_694_, 0);
v___x_700_ = ((size_t)5ULL);
v___x_701_ = ((size_t)1ULL);
v___x_702_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1);
v___x_703_ = lean_usize_land(v_x_695_, v___x_702_);
v_j_704_ = lean_usize_to_nat(v___x_703_);
v___x_705_ = lean_array_get_size(v_es_699_);
v___x_706_ = lean_nat_dec_lt(v_j_704_, v___x_705_);
if (v___x_706_ == 0)
{
lean_dec(v_j_704_);
lean_dec(v_x_698_);
return v_x_694_;
}
else
{
lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_747_; 
lean_inc_ref(v_es_699_);
v_isSharedCheck_747_ = !lean_is_exclusive(v_x_694_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; 
v_unused_748_ = lean_ctor_get(v_x_694_, 0);
lean_dec(v_unused_748_);
v___x_708_ = v_x_694_;
v_isShared_709_ = v_isSharedCheck_747_;
goto v_resetjp_707_;
}
else
{
lean_dec(v_x_694_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_747_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v_v_710_; lean_object* v___x_711_; lean_object* v_xs_x27_712_; lean_object* v___y_714_; 
v_v_710_ = lean_array_fget(v_es_699_, v_j_704_);
v___x_711_ = lean_box(0);
v_xs_x27_712_ = lean_array_fset(v_es_699_, v_j_704_, v___x_711_);
switch(lean_obj_tag(v_v_710_))
{
case 0:
{
lean_object* v_key_719_; lean_object* v_val_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_733_; 
v_key_719_ = lean_ctor_get(v_v_710_, 0);
v_val_720_ = lean_ctor_get(v_v_710_, 1);
v_isSharedCheck_733_ = !lean_is_exclusive(v_v_710_);
if (v_isSharedCheck_733_ == 0)
{
v___x_722_ = v_v_710_;
v_isShared_723_ = v_isSharedCheck_733_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_val_720_);
lean_inc(v_key_719_);
lean_dec(v_v_710_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_733_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
size_t v___x_724_; uint8_t v___x_725_; 
v___x_724_ = lean_unbox_usize(v_key_719_);
v___x_725_ = lean_usize_dec_eq(v_x_697_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
lean_del_object(v___x_722_);
v___x_726_ = lean_box_usize(v_x_697_);
v___x_727_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_719_, v_val_720_, v___x_726_, v_x_698_);
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
v___y_714_ = v___x_728_;
goto v___jp_713_;
}
else
{
lean_object* v___x_729_; lean_object* v___x_731_; 
lean_dec(v_val_720_);
lean_dec(v_key_719_);
v___x_729_ = lean_box_usize(v_x_697_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v_x_698_);
lean_ctor_set(v___x_722_, 0, v___x_729_);
v___x_731_ = v___x_722_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_x_698_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
v___y_714_ = v___x_731_;
goto v___jp_713_;
}
}
}
}
case 1:
{
lean_object* v_node_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_744_; 
v_node_734_ = lean_ctor_get(v_v_710_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v_v_710_);
if (v_isSharedCheck_744_ == 0)
{
v___x_736_ = v_v_710_;
v_isShared_737_ = v_isSharedCheck_744_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_node_734_);
lean_dec(v_v_710_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_744_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
size_t v___x_738_; size_t v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_738_ = lean_usize_shift_right(v_x_695_, v___x_700_);
v___x_739_ = lean_usize_add(v_x_696_, v___x_701_);
v___x_740_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_node_734_, v___x_738_, v___x_739_, v_x_697_, v_x_698_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_740_);
v___x_742_ = v___x_736_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
v___y_714_ = v___x_742_;
goto v___jp_713_;
}
}
}
default: 
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_box_usize(v_x_697_);
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v_x_698_);
v___y_714_ = v___x_746_;
goto v___jp_713_;
}
}
v___jp_713_:
{
lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_715_ = lean_array_fset(v_xs_x27_712_, v_j_704_, v___y_714_);
lean_dec(v_j_704_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v___x_715_);
v___x_717_ = v___x_708_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
else
{
lean_object* v_ks_749_; lean_object* v_vs_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_770_; 
v_ks_749_ = lean_ctor_get(v_x_694_, 0);
v_vs_750_ = lean_ctor_get(v_x_694_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v_x_694_);
if (v_isSharedCheck_770_ == 0)
{
v___x_752_ = v_x_694_;
v_isShared_753_ = v_isSharedCheck_770_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_vs_750_);
lean_inc(v_ks_749_);
lean_dec(v_x_694_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_770_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_ks_749_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_vs_750_);
v___x_755_ = v_reuseFailAlloc_769_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v_newNode_756_; uint8_t v___y_758_; size_t v___x_764_; uint8_t v___x_765_; 
v_newNode_756_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v___x_755_, v_x_697_, v_x_698_);
v___x_764_ = ((size_t)7ULL);
v___x_765_ = lean_usize_dec_le(v___x_764_, v_x_696_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_766_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_756_);
v___x_767_ = lean_unsigned_to_nat(4u);
v___x_768_ = lean_nat_dec_lt(v___x_766_, v___x_767_);
lean_dec(v___x_766_);
v___y_758_ = v___x_768_;
goto v___jp_757_;
}
else
{
v___y_758_ = v___x_765_;
goto v___jp_757_;
}
v___jp_757_:
{
if (v___y_758_ == 0)
{
lean_object* v_ks_759_; lean_object* v_vs_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_ks_759_ = lean_ctor_get(v_newNode_756_, 0);
lean_inc_ref(v_ks_759_);
v_vs_760_ = lean_ctor_get(v_newNode_756_, 1);
lean_inc_ref(v_vs_760_);
lean_dec_ref(v_newNode_756_);
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0);
v___x_763_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_x_696_, v_ks_759_, v_vs_760_, v___x_761_, v___x_762_);
lean_dec_ref(v_vs_760_);
lean_dec_ref(v_ks_759_);
return v___x_763_;
}
else
{
return v_newNode_756_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(size_t v_depth_771_, lean_object* v_keys_772_, lean_object* v_vals_773_, lean_object* v_i_774_, lean_object* v_entries_775_){
_start:
{
lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_776_ = lean_array_get_size(v_keys_772_);
v___x_777_ = lean_nat_dec_lt(v_i_774_, v___x_776_);
if (v___x_777_ == 0)
{
lean_dec(v_i_774_);
return v_entries_775_;
}
else
{
lean_object* v_k_778_; lean_object* v_v_779_; size_t v___x_780_; uint64_t v___x_781_; size_t v_h_782_; size_t v___x_783_; lean_object* v___x_784_; size_t v___x_785_; size_t v___x_786_; size_t v___x_787_; size_t v_h_788_; lean_object* v___x_789_; size_t v___x_790_; lean_object* v___x_791_; 
v_k_778_ = lean_array_fget_borrowed(v_keys_772_, v_i_774_);
v_v_779_ = lean_array_fget_borrowed(v_vals_773_, v_i_774_);
v___x_780_ = lean_unbox_usize(v_k_778_);
v___x_781_ = l_Lean_Lsp_instHashableRpcRef_hash(v___x_780_);
v_h_782_ = lean_uint64_to_usize(v___x_781_);
v___x_783_ = ((size_t)5ULL);
v___x_784_ = lean_unsigned_to_nat(1u);
v___x_785_ = ((size_t)1ULL);
v___x_786_ = lean_usize_sub(v_depth_771_, v___x_785_);
v___x_787_ = lean_usize_mul(v___x_783_, v___x_786_);
v_h_788_ = lean_usize_shift_right(v_h_782_, v___x_787_);
v___x_789_ = lean_nat_add(v_i_774_, v___x_784_);
lean_dec(v_i_774_);
v___x_790_ = lean_unbox_usize(v_k_778_);
lean_inc(v_v_779_);
v___x_791_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_entries_775_, v_h_788_, v_depth_771_, v___x_790_, v_v_779_);
v_i_774_ = v___x_789_;
v_entries_775_ = v___x_791_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_793_, lean_object* v_keys_794_, lean_object* v_vals_795_, lean_object* v_i_796_, lean_object* v_entries_797_){
_start:
{
size_t v_depth_boxed_798_; lean_object* v_res_799_; 
v_depth_boxed_798_ = lean_unbox_usize(v_depth_793_);
lean_dec(v_depth_793_);
v_res_799_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_depth_boxed_798_, v_keys_794_, v_vals_795_, v_i_796_, v_entries_797_);
lean_dec_ref(v_vals_795_);
lean_dec_ref(v_keys_794_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___boxed(lean_object* v_x_800_, lean_object* v_x_801_, lean_object* v_x_802_, lean_object* v_x_803_, lean_object* v_x_804_){
_start:
{
size_t v_x_2249__boxed_805_; size_t v_x_2250__boxed_806_; size_t v_x_2251__boxed_807_; lean_object* v_res_808_; 
v_x_2249__boxed_805_ = lean_unbox_usize(v_x_801_);
lean_dec(v_x_801_);
v_x_2250__boxed_806_ = lean_unbox_usize(v_x_802_);
lean_dec(v_x_802_);
v_x_2251__boxed_807_ = lean_unbox_usize(v_x_803_);
lean_dec(v_x_803_);
v_res_808_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_800_, v_x_2249__boxed_805_, v_x_2250__boxed_806_, v_x_2251__boxed_807_, v_x_804_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(lean_object* v_x_809_, size_t v_x_810_, lean_object* v_x_811_){
_start:
{
uint64_t v___x_812_; size_t v___x_813_; size_t v___x_814_; lean_object* v___x_815_; 
v___x_812_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_810_);
v___x_813_ = lean_uint64_to_usize(v___x_812_);
v___x_814_ = ((size_t)1ULL);
v___x_815_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_809_, v___x_813_, v___x_814_, v_x_810_, v_x_811_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg___boxed(lean_object* v_x_816_, lean_object* v_x_817_, lean_object* v_x_818_){
_start:
{
size_t v_x_2417__boxed_819_; lean_object* v_res_820_; 
v_x_2417__boxed_819_ = lean_unbox_usize(v_x_817_);
lean_dec(v_x_817_);
v_res_820_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(v_x_816_, v_x_2417__boxed_819_, v_x_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcReleaseRef(size_t v_r_821_, lean_object* v_a_822_){
_start:
{
lean_object* v___y_824_; lean_object* v_aliveRefs_828_; lean_object* v_refsById_829_; size_t v_nextRef_830_; uint8_t v_wireFormat_831_; lean_object* v___x_832_; 
v_aliveRefs_828_ = lean_ctor_get(v_a_822_, 0);
v_refsById_829_ = lean_ctor_get(v_a_822_, 1);
v_nextRef_830_ = lean_ctor_get_usize(v_a_822_, 2);
v_wireFormat_831_ = lean_ctor_get_uint8(v_a_822_, sizeof(void*)*3);
lean_inc_ref(v_aliveRefs_828_);
v___x_832_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(v_aliveRefs_828_, v_r_821_);
if (lean_obj_tag(v___x_832_) == 1)
{
lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_860_; 
lean_inc_ref(v_refsById_829_);
lean_inc_ref(v_aliveRefs_828_);
v_isSharedCheck_860_ = !lean_is_exclusive(v_a_822_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; lean_object* v_unused_862_; 
v_unused_861_ = lean_ctor_get(v_a_822_, 1);
lean_dec(v_unused_861_);
v_unused_862_ = lean_ctor_get(v_a_822_, 0);
lean_dec(v_unused_862_);
v___x_834_ = v_a_822_;
v_isShared_835_ = v_isSharedCheck_860_;
goto v_resetjp_833_;
}
else
{
lean_dec(v_a_822_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_860_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v_val_836_; lean_object* v_obj_837_; size_t v_id_838_; lean_object* v_rc_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_859_; 
v_val_836_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_val_836_);
lean_dec_ref(v___x_832_);
v_obj_837_ = lean_ctor_get(v_val_836_, 0);
v_id_838_ = lean_ctor_get_usize(v_val_836_, 2);
v_rc_839_ = lean_ctor_get(v_val_836_, 1);
v_isSharedCheck_859_ = !lean_is_exclusive(v_val_836_);
if (v_isSharedCheck_859_ == 0)
{
v___x_841_ = v_val_836_;
v_isShared_842_ = v_isSharedCheck_859_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_rc_839_);
lean_inc(v_obj_837_);
lean_dec(v_val_836_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_859_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = lean_nat_sub(v_rc_839_, v___x_843_);
lean_dec(v_rc_839_);
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = lean_nat_dec_eq(v___x_844_, v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_848_; 
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v___x_844_);
v___x_848_ = v___x_841_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_obj_837_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v___x_844_);
lean_ctor_set_usize(v_reuseFailAlloc_853_, 2, v_id_838_);
v___x_848_ = v_reuseFailAlloc_853_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_849_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(v_aliveRefs_828_, v_r_821_, v___x_848_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_849_);
v___x_851_ = v___x_834_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_refsById_829_);
lean_ctor_set_usize(v_reuseFailAlloc_852_, 2, v_nextRef_830_);
lean_ctor_set_uint8(v_reuseFailAlloc_852_, sizeof(void*)*3, v_wireFormat_831_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
v___y_824_ = v___x_851_;
goto v___jp_823_;
}
}
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
lean_dec(v___x_844_);
lean_del_object(v___x_841_);
lean_dec(v_obj_837_);
v___x_854_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(v_aliveRefs_828_, v_r_821_);
v___x_855_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(v_refsById_829_, v_id_838_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 1, v___x_855_);
lean_ctor_set(v___x_834_, 0, v___x_854_);
v___x_857_ = v___x_834_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v___x_855_);
lean_ctor_set_usize(v_reuseFailAlloc_858_, 2, v_nextRef_830_);
lean_ctor_set_uint8(v_reuseFailAlloc_858_, sizeof(void*)*3, v_wireFormat_831_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
v___y_824_ = v___x_857_;
goto v___jp_823_;
}
}
}
}
}
else
{
uint8_t v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
lean_dec(v___x_832_);
v___x_863_ = 0;
v___x_864_ = lean_box(v___x_863_);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v_a_822_);
return v___x_865_;
}
v___jp_823_:
{
uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = 1;
v___x_826_ = lean_box(v___x_825_);
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
lean_ctor_set(v___x_827_, 1, v___y_824_);
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcReleaseRef___boxed(lean_object* v_r_866_, lean_object* v_a_867_){
_start:
{
size_t v_r_boxed_868_; lean_object* v_res_869_; 
v_r_boxed_868_ = lean_unbox_usize(v_r_866_);
lean_dec(v_r_866_);
v_res_869_ = l_Lean_Server_rpcReleaseRef(v_r_boxed_868_, v_a_867_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0(lean_object* v_00_u03b2_870_, lean_object* v_x_871_, size_t v_x_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(v_x_871_, v_x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___boxed(lean_object* v_00_u03b2_874_, lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
size_t v_x_2509__boxed_877_; lean_object* v_res_878_; 
v_x_2509__boxed_877_ = lean_unbox_usize(v_x_876_);
lean_dec(v_x_876_);
v_res_878_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0(v_00_u03b2_874_, v_x_875_, v_x_2509__boxed_877_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1(lean_object* v_00_u03b2_879_, lean_object* v_x_880_, size_t v_x_881_, lean_object* v_x_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(v_x_880_, v_x_881_, v_x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___boxed(lean_object* v_00_u03b2_884_, lean_object* v_x_885_, lean_object* v_x_886_, lean_object* v_x_887_){
_start:
{
size_t v_x_2517__boxed_888_; lean_object* v_res_889_; 
v_x_2517__boxed_888_ = lean_unbox_usize(v_x_886_);
lean_dec(v_x_886_);
v_res_889_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1(v_00_u03b2_884_, v_x_885_, v_x_2517__boxed_888_, v_x_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2(lean_object* v_00_u03b2_890_, lean_object* v_x_891_, size_t v_x_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(v_x_891_, v_x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___boxed(lean_object* v_00_u03b2_894_, lean_object* v_x_895_, lean_object* v_x_896_){
_start:
{
size_t v_x_2528__boxed_897_; lean_object* v_res_898_; 
v_x_2528__boxed_897_ = lean_unbox_usize(v_x_896_);
lean_dec(v_x_896_);
v_res_898_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2(v_00_u03b2_894_, v_x_895_, v_x_2528__boxed_897_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3(lean_object* v_00_u03b2_899_, lean_object* v_x_900_, size_t v_x_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(v_x_900_, v_x_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___boxed(lean_object* v_00_u03b2_903_, lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
size_t v_x_2536__boxed_906_; lean_object* v_res_907_; 
v_x_2536__boxed_906_ = lean_unbox_usize(v_x_905_);
lean_dec(v_x_905_);
v_res_907_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3(v_00_u03b2_903_, v_x_904_, v_x_2536__boxed_906_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0(lean_object* v_00_u03b2_908_, lean_object* v_x_909_, size_t v_x_910_, size_t v_x_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_909_, v_x_910_, v_x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___boxed(lean_object* v_00_u03b2_913_, lean_object* v_x_914_, lean_object* v_x_915_, lean_object* v_x_916_){
_start:
{
size_t v_x_2544__boxed_917_; size_t v_x_2545__boxed_918_; lean_object* v_res_919_; 
v_x_2544__boxed_917_ = lean_unbox_usize(v_x_915_);
lean_dec(v_x_915_);
v_x_2545__boxed_918_ = lean_unbox_usize(v_x_916_);
lean_dec(v_x_916_);
v_res_919_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0(v_00_u03b2_913_, v_x_914_, v_x_2544__boxed_917_, v_x_2545__boxed_918_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2(lean_object* v_00_u03b2_920_, lean_object* v_x_921_, size_t v_x_922_, size_t v_x_923_, size_t v_x_924_, lean_object* v_x_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_921_, v_x_922_, v_x_923_, v_x_924_, v_x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___boxed(lean_object* v_00_u03b2_927_, lean_object* v_x_928_, lean_object* v_x_929_, lean_object* v_x_930_, lean_object* v_x_931_, lean_object* v_x_932_){
_start:
{
size_t v_x_2555__boxed_933_; size_t v_x_2556__boxed_934_; size_t v_x_2557__boxed_935_; lean_object* v_res_936_; 
v_x_2555__boxed_933_ = lean_unbox_usize(v_x_929_);
lean_dec(v_x_929_);
v_x_2556__boxed_934_ = lean_unbox_usize(v_x_930_);
lean_dec(v_x_930_);
v_x_2557__boxed_935_ = lean_unbox_usize(v_x_931_);
lean_dec(v_x_931_);
v_res_936_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2(v_00_u03b2_927_, v_x_928_, v_x_2555__boxed_933_, v_x_2556__boxed_934_, v_x_2557__boxed_935_, v_x_932_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4(lean_object* v_00_u03b2_937_, lean_object* v_x_938_, size_t v_x_939_, size_t v_x_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_x_938_, v_x_939_, v_x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___boxed(lean_object* v_00_u03b2_942_, lean_object* v_x_943_, lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
size_t v_x_2572__boxed_946_; size_t v_x_2573__boxed_947_; lean_object* v_res_948_; 
v_x_2572__boxed_946_ = lean_unbox_usize(v_x_944_);
lean_dec(v_x_944_);
v_x_2573__boxed_947_ = lean_unbox_usize(v_x_945_);
lean_dec(v_x_945_);
v_res_948_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4(v_00_u03b2_942_, v_x_943_, v_x_2572__boxed_946_, v_x_2573__boxed_947_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6(lean_object* v_00_u03b2_949_, lean_object* v_x_950_, size_t v_x_951_, size_t v_x_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_950_, v_x_951_, v_x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___boxed(lean_object* v_00_u03b2_954_, lean_object* v_x_955_, lean_object* v_x_956_, lean_object* v_x_957_){
_start:
{
size_t v_x_2583__boxed_958_; size_t v_x_2584__boxed_959_; lean_object* v_res_960_; 
v_x_2583__boxed_958_ = lean_unbox_usize(v_x_956_);
lean_dec(v_x_956_);
v_x_2584__boxed_959_ = lean_unbox_usize(v_x_957_);
lean_dec(v_x_957_);
v_res_960_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6(v_00_u03b2_954_, v_x_955_, v_x_2583__boxed_958_, v_x_2584__boxed_959_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_961_, lean_object* v_keys_962_, lean_object* v_vals_963_, lean_object* v_heq_964_, lean_object* v_i_965_, size_t v_k_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(v_keys_962_, v_vals_963_, v_i_965_, v_k_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_968_, lean_object* v_keys_969_, lean_object* v_vals_970_, lean_object* v_heq_971_, lean_object* v_i_972_, lean_object* v_k_973_){
_start:
{
size_t v_k_boxed_974_; lean_object* v_res_975_; 
v_k_boxed_974_ = lean_unbox_usize(v_k_973_);
lean_dec(v_k_973_);
v_res_975_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1(v_00_u03b2_968_, v_keys_969_, v_vals_970_, v_heq_971_, v_i_972_, v_k_boxed_974_);
lean_dec_ref(v_vals_970_);
lean_dec_ref(v_keys_969_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_976_, lean_object* v_n_977_, size_t v_k_978_, lean_object* v_v_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v_n_977_, v_k_978_, v_v_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_981_, lean_object* v_n_982_, lean_object* v_k_983_, lean_object* v_v_984_){
_start:
{
size_t v_k_boxed_985_; lean_object* v_res_986_; 
v_k_boxed_985_ = lean_unbox_usize(v_k_983_);
lean_dec(v_k_983_);
v_res_986_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4(v_00_u03b2_981_, v_n_982_, v_k_boxed_985_, v_v_984_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_987_, size_t v_depth_988_, lean_object* v_keys_989_, lean_object* v_vals_990_, lean_object* v_heq_991_, lean_object* v_i_992_, lean_object* v_entries_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_depth_988_, v_keys_989_, v_vals_990_, v_i_992_, v_entries_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_995_, lean_object* v_depth_996_, lean_object* v_keys_997_, lean_object* v_vals_998_, lean_object* v_heq_999_, lean_object* v_i_1000_, lean_object* v_entries_1001_){
_start:
{
size_t v_depth_boxed_1002_; lean_object* v_res_1003_; 
v_depth_boxed_1002_ = lean_unbox_usize(v_depth_996_);
lean_dec(v_depth_996_);
v_res_1003_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5(v_00_u03b2_995_, v_depth_boxed_1002_, v_keys_997_, v_vals_998_, v_heq_999_, v_i_1000_, v_entries_1001_);
lean_dec_ref(v_vals_998_);
lean_dec_ref(v_keys_997_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_1004_, lean_object* v_x_1005_, lean_object* v_x_1006_, size_t v_x_1007_, lean_object* v_x_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_x_1005_, v_x_1006_, v_x_1007_, v_x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1010_, lean_object* v_x_1011_, lean_object* v_x_1012_, lean_object* v_x_1013_, lean_object* v_x_1014_){
_start:
{
size_t v_x_2601__boxed_1015_; lean_object* v_res_1016_; 
v_x_2601__boxed_1015_ = lean_unbox_usize(v_x_1013_);
lean_dec(v_x_1013_);
v_res_1016_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7(v_00_u03b2_1010_, v_x_1011_, v_x_1012_, v_x_2601__boxed_1015_, v_x_1014_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__0(lean_object* v_inst_1017_, lean_object* v_a_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_apply_1(v_inst_1017_, v_a_1018_);
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set(v___x_1021_, 1, v___y_1019_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1(lean_object* v_inst_1022_, lean_object* v___x_1023_, lean_object* v___x_1024_, lean_object* v_j_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_201__overap_1028_; lean_object* v___x_1029_; 
v___x_1027_ = lean_apply_1(v_inst_1022_, v_j_1025_);
v___x_201__overap_1028_ = l_MonadExcept_ofExcept___redArg(v___x_1023_, v___x_1024_, v___x_1027_);
lean_inc_ref(v___y_1026_);
v___x_1029_ = lean_apply_1(v___x_201__overap_1028_, v___y_1026_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1___boxed(lean_object* v_inst_1030_, lean_object* v___x_1031_, lean_object* v___x_1032_, lean_object* v_j_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1(v_inst_1030_, v___x_1031_, v___x_1032_, v_j_1033_, v___y_1034_);
lean_dec_ref(v___y_1034_);
return v_res_1035_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9));
v___x_1056_ = l_ReaderT_instMonad___redArg(v___x_1055_);
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___f_1058_; 
v___x_1057_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___f_1058_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1058_, 0, v___x_1057_);
return v___f_1058_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___f_1060_; 
v___x_1059_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___f_1060_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_1060_, 0, v___x_1059_);
return v___f_1060_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___f_1062_; 
v___x_1061_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___f_1062_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_1062_, 0, v___x_1061_);
return v___f_1062_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___f_1064_; 
v___x_1063_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___f_1064_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_1064_, 0, v___x_1063_);
return v___f_1064_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1066_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_1066_, 0, lean_box(0));
lean_closure_set(v___x_1066_, 1, lean_box(0));
lean_closure_set(v___x_1066_, 2, v___x_1065_);
return v___x_1066_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16(void){
_start:
{
lean_object* v___f_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___f_1067_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11);
v___x_1068_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v___f_1067_);
return v___x_1069_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1071_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_1071_, 0, lean_box(0));
lean_closure_set(v___x_1071_, 1, lean_box(0));
lean_closure_set(v___x_1071_, 2, v___x_1070_);
return v___x_1071_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18(void){
_start:
{
lean_object* v___f_1072_; lean_object* v___f_1073_; lean_object* v___f_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___f_1072_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14);
v___f_1073_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13);
v___f_1074_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12);
v___x_1075_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17);
v___x_1076_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16);
v___x_1077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v___x_1075_);
lean_ctor_set(v___x_1077_, 2, v___f_1074_);
lean_ctor_set(v___x_1077_, 3, v___f_1073_);
lean_ctor_set(v___x_1077_, 4, v___f_1072_);
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1079_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_1079_, 0, lean_box(0));
lean_closure_set(v___x_1079_, 1, lean_box(0));
lean_closure_set(v___x_1079_, 2, v___x_1078_);
return v___x_1079_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1080_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19);
v___x_1081_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18);
v___x_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v___x_1080_);
return v___x_1082_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1084_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch), 6, 3);
lean_closure_set(v___x_1084_, 0, lean_box(0));
lean_closure_set(v___x_1084_, 1, lean_box(0));
lean_closure_set(v___x_1084_, 2, v___x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg(lean_object* v_inst_1085_, lean_object* v_inst_1086_){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v_toApplicative_1089_; lean_object* v_toPure_1090_; lean_object* v___f_1091_; lean_object* v___f_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___f_1096_; lean_object* v___x_1097_; 
v___x_1087_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1088_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20);
v_toApplicative_1089_ = lean_ctor_get(v___x_1087_, 0);
v_toPure_1090_ = lean_ctor_get(v_toApplicative_1089_, 1);
v___f_1091_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1091_, 0, v_inst_1086_);
lean_inc(v_toPure_1090_);
v___f_1092_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptTOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1092_, 0, v_toPure_1090_);
v___x_1093_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21);
v___x_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___f_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_1094_);
v___f_1096_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1096_, 0, v_inst_1085_);
lean_closure_set(v___f_1096_, 1, v___x_1088_);
lean_closure_set(v___f_1096_, 2, v___x_1095_);
v___x_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___f_1091_);
lean_ctor_set(v___x_1097_, 1, v___f_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson(lean_object* v_00_u03b1_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg(v_inst_1099_, v_inst_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg___lam__0(lean_object* v_inst_1102_, lean_object* v___x_1103_, lean_object* v_v_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_fst_1107_; lean_object* v_snd_1108_; 
if (lean_obj_tag(v_v_1104_) == 0)
{
lean_object* v___x_1111_; 
lean_dec_ref(v_inst_1102_);
v___x_1111_ = lean_box(0);
v_fst_1107_ = v___x_1111_;
v_snd_1108_ = v___y_1105_;
goto v___jp_1106_;
}
else
{
lean_object* v_rpcEncode_1112_; lean_object* v_val_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1123_; 
v_rpcEncode_1112_ = lean_ctor_get(v_inst_1102_, 0);
lean_inc_ref(v_rpcEncode_1112_);
lean_dec_ref(v_inst_1102_);
v_val_1113_ = lean_ctor_get(v_v_1104_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_v_1104_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1115_ = v_v_1104_;
v_isShared_1116_ = v_isSharedCheck_1123_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_val_1113_);
lean_dec(v_v_1104_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1123_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v_fst_1118_; lean_object* v_snd_1119_; lean_object* v___x_1121_; 
v___x_1117_ = lean_apply_2(v_rpcEncode_1112_, v_val_1113_, v___y_1105_);
v_fst_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_fst_1118_);
v_snd_1119_ = lean_ctor_get(v___x_1117_, 1);
lean_inc(v_snd_1119_);
lean_dec_ref(v___x_1117_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v_fst_1118_);
v___x_1121_ = v___x_1115_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_fst_1118_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
v_fst_1107_ = v___x_1121_;
v_snd_1108_ = v_snd_1119_;
goto v___jp_1106_;
}
}
}
v___jp_1106_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = l_Option_toJson___redArg(v___x_1103_, v_fst_1107_);
v___x_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
lean_ctor_set(v___x_1110_, 1, v_snd_1108_);
return v___x_1110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg___lam__1(lean_object* v___f_1126_, lean_object* v_inst_1127_, lean_object* v_j_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Option_fromJson_x3f___redArg(v___f_1126_, v_j_1128_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec_ref(v_inst_1127_);
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
else
{
lean_object* v_a_1139_; 
v_a_1139_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1139_);
lean_dec_ref(v___x_1130_);
if (lean_obj_tag(v_a_1139_) == 0)
{
lean_object* v___x_1140_; 
lean_dec_ref(v_inst_1127_);
v___x_1140_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___lam__1___closed__0));
return v___x_1140_;
}
else
{
lean_object* v_rpcDecode_1141_; lean_object* v_val_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1166_; 
v_rpcDecode_1141_ = lean_ctor_get(v_inst_1127_, 1);
lean_inc_ref(v_rpcDecode_1141_);
lean_dec_ref(v_inst_1127_);
v_val_1142_ = lean_ctor_get(v_a_1139_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_a_1139_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1144_ = v_a_1139_;
v_isShared_1145_ = v_isSharedCheck_1166_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_val_1142_);
lean_dec(v_a_1139_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1166_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; 
lean_inc_ref(v___y_1129_);
v___x_1146_ = lean_apply_2(v_rpcDecode_1141_, v_val_1142_, v___y_1129_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_del_object(v___x_1144_);
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1165_; 
v_a_1155_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1157_ = v___x_1146_;
v_isShared_1158_ = v_isSharedCheck_1165_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1146_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1165_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v_a_1155_);
v___x_1160_ = v___x_1144_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1162_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1160_);
v___x_1162_ = v___x_1157_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg___lam__1___boxed(lean_object* v___f_1167_, lean_object* v_inst_1168_, lean_object* v_j_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_Server_instRpcEncodableOption___redArg___lam__1(v___f_1167_, v_inst_1168_, v_j_1169_, v___y_1170_);
lean_dec_ref(v___y_1170_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg(lean_object* v_inst_1174_){
_start:
{
lean_object* v___x_1175_; lean_object* v___f_1176_; lean_object* v___f_1177_; lean_object* v___f_1178_; lean_object* v___x_1179_; 
v___x_1175_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__0));
lean_inc_ref(v_inst_1174_);
v___f_1176_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOption___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1176_, 0, v_inst_1174_);
lean_closure_set(v___f_1176_, 1, v___x_1175_);
v___f_1177_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__1));
v___f_1178_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOption___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1178_, 0, v___f_1177_);
lean_closure_set(v___f_1178_, 1, v_inst_1174_);
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___f_1176_);
lean_ctor_set(v___x_1179_, 1, v___f_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption(lean_object* v_00_u03b1_1180_, lean_object* v_inst_1181_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = l_Lean_Server_instRpcEncodableOption___redArg(v_inst_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__0(lean_object* v_inst_1183_, lean_object* v___x_1184_, lean_object* v___x_1185_, lean_object* v_a_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_rpcEncode_1188_; size_t v_sz_1189_; size_t v___x_1190_; lean_object* v___x_648__overap_1191_; lean_object* v___x_1192_; lean_object* v_fst_1193_; lean_object* v_snd_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1202_; 
v_rpcEncode_1188_ = lean_ctor_get(v_inst_1183_, 0);
lean_inc_ref(v_rpcEncode_1188_);
lean_dec_ref(v_inst_1183_);
v_sz_1189_ = lean_array_size(v_a_1186_);
v___x_1190_ = ((size_t)0ULL);
v___x_648__overap_1191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1184_, v_rpcEncode_1188_, v_sz_1189_, v___x_1190_, v_a_1186_);
v___x_1192_ = lean_apply_1(v___x_648__overap_1191_, v___y_1187_);
v_fst_1193_ = lean_ctor_get(v___x_1192_, 0);
v_snd_1194_ = lean_ctor_get(v___x_1192_, 1);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1196_ = v___x_1192_;
v_isShared_1197_ = v_isSharedCheck_1202_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_snd_1194_);
lean_inc(v_fst_1193_);
lean_dec(v___x_1192_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1202_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1198_ = l_Array_toJson___redArg(v___x_1185_, v_fst_1193_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1198_);
v___x_1200_ = v___x_1196_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_snd_1194_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__1(lean_object* v___f_1203_, lean_object* v_inst_1204_, lean_object* v___x_1205_, lean_object* v_b_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Array_fromJson_x3f___redArg(v___f_1203_, v_b_1206_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec_ref(v___x_1205_);
lean_dec_ref(v_inst_1204_);
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1208_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1208_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
else
{
lean_object* v_a_1217_; lean_object* v_rpcDecode_1218_; size_t v_sz_1219_; size_t v___x_1220_; lean_object* v___x_662__overap_1221_; lean_object* v___x_1222_; 
v_a_1217_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_a_1217_);
lean_dec_ref(v___x_1208_);
v_rpcDecode_1218_ = lean_ctor_get(v_inst_1204_, 1);
lean_inc_ref(v_rpcDecode_1218_);
lean_dec_ref(v_inst_1204_);
v_sz_1219_ = lean_array_size(v_a_1217_);
v___x_1220_ = ((size_t)0ULL);
v___x_662__overap_1221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1205_, v_rpcDecode_1218_, v_sz_1219_, v___x_1220_, v_a_1217_);
lean_inc_ref(v___y_1207_);
v___x_1222_ = lean_apply_1(v___x_662__overap_1221_, v___y_1207_);
return v___x_1222_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__1___boxed(lean_object* v___f_1223_, lean_object* v_inst_1224_, lean_object* v___x_1225_, lean_object* v_b_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_Server_instRpcEncodableArray___redArg___lam__1(v___f_1223_, v_inst_1224_, v___x_1225_, v_b_1226_, v___y_1227_);
lean_dec_ref(v___y_1227_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg(lean_object* v_inst_1255_){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___f_1258_; lean_object* v___x_1259_; lean_object* v___f_1260_; lean_object* v___f_1261_; lean_object* v___x_1262_; 
v___x_1256_ = ((lean_object*)(l_Lean_Server_instRpcEncodableArray___redArg___closed__9));
v___x_1257_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__0));
lean_inc_ref(v_inst_1255_);
v___f_1258_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableArray___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1258_, 0, v_inst_1255_);
lean_closure_set(v___f_1258_, 1, v___x_1256_);
lean_closure_set(v___f_1258_, 2, v___x_1257_);
v___x_1259_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20);
v___f_1260_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__1));
v___f_1261_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableArray___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1261_, 0, v___f_1260_);
lean_closure_set(v___f_1261_, 1, v_inst_1255_);
lean_closure_set(v___f_1261_, 2, v___x_1259_);
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___f_1258_);
lean_ctor_set(v___x_1262_, 1, v___f_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray(lean_object* v_00_u03b1_1263_, lean_object* v_inst_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_Server_instRpcEncodableArray___redArg(v_inst_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg___lam__0(lean_object* v_inst_1266_, lean_object* v_inst_1267_, lean_object* v___x_1268_, lean_object* v_x_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_fst_1271_; lean_object* v_snd_1272_; lean_object* v_rpcEncode_1273_; lean_object* v___x_1274_; lean_object* v_fst_1275_; lean_object* v_snd_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1295_; 
v_fst_1271_ = lean_ctor_get(v_x_1269_, 0);
lean_inc(v_fst_1271_);
v_snd_1272_ = lean_ctor_get(v_x_1269_, 1);
lean_inc(v_snd_1272_);
lean_dec_ref(v_x_1269_);
v_rpcEncode_1273_ = lean_ctor_get(v_inst_1266_, 0);
lean_inc_ref(v_rpcEncode_1273_);
lean_dec_ref(v_inst_1266_);
v___x_1274_ = lean_apply_2(v_rpcEncode_1273_, v_fst_1271_, v___y_1270_);
v_fst_1275_ = lean_ctor_get(v___x_1274_, 0);
v_snd_1276_ = lean_ctor_get(v___x_1274_, 1);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1278_ = v___x_1274_;
v_isShared_1279_ = v_isSharedCheck_1295_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_snd_1276_);
lean_inc(v_fst_1275_);
lean_dec(v___x_1274_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1295_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v_rpcEncode_1280_; lean_object* v___x_1281_; lean_object* v_fst_1282_; lean_object* v_snd_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1294_; 
v_rpcEncode_1280_ = lean_ctor_get(v_inst_1267_, 0);
lean_inc_ref(v_rpcEncode_1280_);
lean_dec_ref(v_inst_1267_);
v___x_1281_ = lean_apply_2(v_rpcEncode_1280_, v_snd_1272_, v_snd_1276_);
v_fst_1282_ = lean_ctor_get(v___x_1281_, 0);
v_snd_1283_ = lean_ctor_get(v___x_1281_, 1);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1285_ = v___x_1281_;
v_isShared_1286_ = v_isSharedCheck_1294_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_snd_1283_);
lean_inc(v_fst_1282_);
lean_dec(v___x_1281_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1294_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v_fst_1282_);
lean_ctor_set(v___x_1285_, 0, v_fst_1275_);
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_fst_1275_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_fst_1282_);
v___x_1288_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1289_; lean_object* v___x_1291_; 
lean_inc_ref(v___x_1268_);
v___x_1289_ = l_Prod_toJson___redArg(v___x_1268_, v___x_1268_, v___x_1288_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 1, v_snd_1283_);
lean_ctor_set(v___x_1278_, 0, v___x_1289_);
v___x_1291_ = v___x_1278_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_snd_1283_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg___lam__1(lean_object* v___f_1296_, lean_object* v_inst_1297_, lean_object* v_inst_1298_, lean_object* v_j_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v___x_1301_; 
lean_inc_ref(v___f_1296_);
v___x_1301_ = l_Prod_fromJson_x3f___redArg(v___f_1296_, v___f_1296_, v_j_1299_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec_ref(v_inst_1298_);
lean_dec_ref(v_inst_1297_);
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
lean_object* v_a_1310_; lean_object* v_fst_1311_; lean_object* v_snd_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1348_; 
v_a_1310_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1310_);
lean_dec_ref(v___x_1301_);
v_fst_1311_ = lean_ctor_get(v_a_1310_, 0);
v_snd_1312_ = lean_ctor_get(v_a_1310_, 1);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_a_1310_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1314_ = v_a_1310_;
v_isShared_1315_ = v_isSharedCheck_1348_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_snd_1312_);
lean_inc(v_fst_1311_);
lean_dec(v_a_1310_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1348_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v_rpcDecode_1316_; lean_object* v___x_1317_; 
v_rpcDecode_1316_ = lean_ctor_get(v_inst_1297_, 1);
lean_inc_ref(v_rpcDecode_1316_);
lean_dec_ref(v_inst_1297_);
lean_inc_ref(v___y_1300_);
v___x_1317_ = lean_apply_2(v_rpcDecode_1316_, v_fst_1311_, v___y_1300_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_del_object(v___x_1314_);
lean_dec(v_snd_1312_);
lean_dec_ref(v_inst_1298_);
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v_rpcDecode_1327_; lean_object* v___x_1328_; 
v_a_1326_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_a_1326_);
lean_dec_ref(v___x_1317_);
v_rpcDecode_1327_ = lean_ctor_get(v_inst_1298_, 1);
lean_inc_ref(v_rpcDecode_1327_);
lean_dec_ref(v_inst_1298_);
lean_inc_ref(v___y_1300_);
v___x_1328_ = lean_apply_2(v_rpcDecode_1327_, v_snd_1312_, v___y_1300_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec(v_a_1326_);
lean_del_object(v___x_1314_);
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
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
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1347_; 
v_a_1337_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1339_ = v___x_1328_;
v_isShared_1340_ = v_isSharedCheck_1347_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1328_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1347_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 1, v_a_1337_);
lean_ctor_set(v___x_1314_, 0, v_a_1326_);
v___x_1342_ = v___x_1314_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1326_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1344_; 
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1342_);
v___x_1344_ = v___x_1339_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg___lam__1___boxed(lean_object* v___f_1349_, lean_object* v_inst_1350_, lean_object* v_inst_1351_, lean_object* v_j_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Lean_Server_instRpcEncodableProd___redArg___lam__1(v___f_1349_, v_inst_1350_, v_inst_1351_, v_j_1352_, v___y_1353_);
lean_dec_ref(v___y_1353_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg(lean_object* v_inst_1355_, lean_object* v_inst_1356_){
_start:
{
lean_object* v___x_1357_; lean_object* v___f_1358_; lean_object* v___f_1359_; lean_object* v___f_1360_; lean_object* v___x_1361_; 
v___x_1357_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__0));
lean_inc_ref(v_inst_1356_);
lean_inc_ref(v_inst_1355_);
v___f_1358_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableProd___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1358_, 0, v_inst_1355_);
lean_closure_set(v___f_1358_, 1, v_inst_1356_);
lean_closure_set(v___f_1358_, 2, v___x_1357_);
v___f_1359_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__1));
v___f_1360_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableProd___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1360_, 0, v___f_1359_);
lean_closure_set(v___f_1360_, 1, v_inst_1355_);
lean_closure_set(v___f_1360_, 2, v_inst_1356_);
v___x_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___f_1358_);
lean_ctor_set(v___x_1361_, 1, v___f_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd(lean_object* v_00_u03b1_1362_, lean_object* v_00_u03b2_1363_, lean_object* v_inst_1364_, lean_object* v_inst_1365_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Lean_Server_instRpcEncodableProd___redArg(v_inst_1364_, v_inst_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__0(lean_object* v_inst_1367_, lean_object* v_fn_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v_rpcEncode_1370_; lean_object* v___x_1371_; lean_object* v_fst_1372_; lean_object* v_snd_1373_; lean_object* v___x_1374_; 
v_rpcEncode_1370_ = lean_ctor_get(v_inst_1367_, 0);
lean_inc_ref(v_rpcEncode_1370_);
lean_dec_ref(v_inst_1367_);
v___x_1371_ = lean_apply_1(v_fn_1368_, v___y_1369_);
v_fst_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_fst_1372_);
v_snd_1373_ = lean_ctor_get(v___x_1371_, 1);
lean_inc(v_snd_1373_);
lean_dec_ref(v___x_1371_);
v___x_1374_ = lean_apply_2(v_rpcEncode_1370_, v_fst_1372_, v_snd_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1(lean_object* v_inst_1375_, lean_object* v___x_1376_, lean_object* v_j_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_rpcDecode_1379_; lean_object* v___x_1380_; 
v_rpcDecode_1379_ = lean_ctor_get(v_inst_1375_, 1);
lean_inc_ref(v_rpcDecode_1379_);
lean_dec_ref(v_inst_1375_);
lean_inc_ref(v___y_1378_);
v___x_1380_ = lean_apply_2(v_rpcDecode_1379_, v_j_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec_ref(v___x_1376_);
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1380_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
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
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1397_; 
v_a_1389_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1391_ = v___x_1380_;
v_isShared_1392_ = v_isSharedCheck_1397_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1380_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1397_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1393_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 5);
lean_closure_set(v___x_1393_, 0, lean_box(0));
lean_closure_set(v___x_1393_, 1, lean_box(0));
lean_closure_set(v___x_1393_, 2, v___x_1376_);
lean_closure_set(v___x_1393_, 3, lean_box(0));
lean_closure_set(v___x_1393_, 4, v_a_1389_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1393_);
v___x_1395_ = v___x_1391_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1___boxed(lean_object* v_inst_1398_, lean_object* v___x_1399_, lean_object* v_j_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1(v_inst_1398_, v___x_1399_, v_j_1400_, v___y_1401_);
lean_dec_ref(v___y_1401_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg(lean_object* v_inst_1403_){
_start:
{
lean_object* v___f_1404_; lean_object* v___x_1405_; lean_object* v___f_1406_; lean_object* v___x_1407_; 
lean_inc_ref(v_inst_1403_);
v___f_1404_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1404_, 0, v_inst_1403_);
v___x_1405_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9));
v___f_1406_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1406_, 0, v_inst_1403_);
lean_closure_set(v___f_1406_, 1, v___x_1405_);
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___f_1404_);
lean_ctor_set(v___x_1407_, 1, v___f_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore(lean_object* v_00_u03b1_1408_, lean_object* v_inst_1409_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg(v_inst_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(lean_object* v_inst_1411_, lean_object* v_r_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v___x_1414_; lean_object* v_fst_1415_; lean_object* v_snd_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1435_; 
v___x_1414_ = l_Lean_Server_rpcStoreRef___redArg(v_inst_1411_, v_r_1412_, v_a_1413_);
v_fst_1415_ = lean_ctor_get(v___x_1414_, 0);
v_snd_1416_ = lean_ctor_get(v___x_1414_, 1);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1418_ = v___x_1414_;
v_isShared_1419_ = v_isSharedCheck_1435_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_snd_1416_);
lean_inc(v_fst_1415_);
lean_dec(v___x_1414_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1435_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___y_1421_; uint8_t v_wireFormat_1432_; 
v_wireFormat_1432_ = lean_ctor_get_uint8(v_snd_1416_, sizeof(void*)*3);
if (v_wireFormat_1432_ == 0)
{
lean_object* v___x_1433_; 
v___x_1433_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0));
v___y_1421_ = v___x_1433_;
goto v___jp_1420_;
}
else
{
lean_object* v___x_1434_; 
v___x_1434_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1));
v___y_1421_ = v___x_1434_;
goto v___jp_1420_;
}
v___jp_1420_:
{
size_t v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1422_ = lean_unbox_usize(v_fst_1415_);
lean_dec(v_fst_1415_);
v___x_1423_ = lean_usize_to_nat(v___x_1422_);
v___x_1424_ = l_Lean_bignumToJson(v___x_1423_);
lean_inc_ref(v___y_1421_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 1, v___x_1424_);
lean_ctor_set(v___x_1418_, 0, v___y_1421_);
v___x_1426_ = v___x_1418_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___y_1421_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1427_ = lean_box(0);
v___x_1428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1426_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
v___x_1429_ = l_Lean_Json_mkObj(v___x_1428_);
v___x_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
lean_ctor_set(v___x_1430_, 1, v_snd_1416_);
return v___x_1430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg___boxed(lean_object* v_inst_1436_, lean_object* v_r_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(v_inst_1436_, v_r_1437_, v_a_1438_);
lean_dec_ref(v_r_1437_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode(lean_object* v_00_u03b1_1440_, lean_object* v_inst_1441_, lean_object* v_r_1442_, lean_object* v_a_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(v_inst_1441_, v_r_1442_, v_a_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___boxed(lean_object* v_00_u03b1_1445_, lean_object* v_inst_1446_, lean_object* v_r_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode(v_00_u03b1_1445_, v_inst_1446_, v_r_1447_, v_a_1448_);
lean_dec_ref(v_r_1447_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(lean_object* v_inst_1451_, lean_object* v_j_1452_, lean_object* v_a_1453_){
_start:
{
uint8_t v_wireFormat_1454_; lean_object* v___x_1455_; lean_object* v___y_1457_; 
v_wireFormat_1454_ = lean_ctor_get_uint8(v_a_1453_, sizeof(void*)*3);
v___x_1455_ = ((lean_object*)(l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg___closed__0));
if (v_wireFormat_1454_ == 0)
{
lean_object* v___x_1470_; 
v___x_1470_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0));
v___y_1457_ = v___x_1470_;
goto v___jp_1456_;
}
else
{
lean_object* v___x_1471_; 
v___x_1471_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1));
v___y_1457_ = v___x_1471_;
goto v___jp_1456_;
}
v___jp_1456_:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1452_, v___x_1455_, v___y_1457_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
lean_dec(v_inst_1451_);
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1458_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1458_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
else
{
lean_object* v_a_1467_; size_t v___x_1468_; lean_object* v___x_1469_; 
v_a_1467_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1467_);
lean_dec_ref(v___x_1458_);
v___x_1468_ = lean_unbox_usize(v_a_1467_);
lean_dec(v_a_1467_);
v___x_1469_ = l_Lean_Server_rpcGetRef___redArg(v_inst_1451_, v___x_1468_, v_a_1453_);
return v___x_1469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg___boxed(lean_object* v_inst_1472_, lean_object* v_j_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v_inst_1472_, v_j_1473_, v_a_1474_);
lean_dec_ref(v_a_1474_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode(lean_object* v_00_u03b1_1476_, lean_object* v_inst_1477_, lean_object* v_j_1478_, lean_object* v_a_1479_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v_inst_1477_, v_j_1478_, v_a_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___boxed(lean_object* v_00_u03b1_1481_, lean_object* v_inst_1482_, lean_object* v_j_1483_, lean_object* v_a_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode(v_00_u03b1_1481_, v_inst_1482_, v_j_1483_, v_a_1484_);
lean_dec_ref(v_a_1484_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName___redArg(lean_object* v_inst_1486_){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_inc(v_inst_1486_);
v___x_1487_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___boxed), 4, 2);
lean_closure_set(v___x_1487_, 0, lean_box(0));
lean_closure_set(v___x_1487_, 1, v_inst_1486_);
v___x_1488_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___boxed), 4, 2);
lean_closure_set(v___x_1488_, 0, lean_box(0));
lean_closure_set(v___x_1488_, 1, v_inst_1486_);
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1487_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName(lean_object* v_00_u03b1_1490_, lean_object* v_inst_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName___redArg(v_inst_1491_);
return v___x_1492_;
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
