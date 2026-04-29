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
lean_object* v_es_488_; lean_object* v___x_489_; size_t v___x_490_; size_t v___x_491_; size_t v___x_492_; lean_object* v_j_493_; lean_object* v___x_494_; 
v_es_488_ = lean_ctor_get(v_x_485_, 0);
v___x_489_ = lean_box(2);
v___x_490_ = ((size_t)5ULL);
v___x_491_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1);
v___x_492_ = lean_usize_land(v_x_486_, v___x_491_);
v_j_493_ = lean_usize_to_nat(v___x_492_);
v___x_494_ = lean_array_get_borrowed(v___x_489_, v_es_488_, v_j_493_);
lean_dec(v_j_493_);
switch(lean_obj_tag(v___x_494_))
{
case 0:
{
lean_object* v_key_495_; lean_object* v_val_496_; size_t v___x_497_; uint8_t v___x_498_; 
v_key_495_ = lean_ctor_get(v___x_494_, 0);
v_val_496_ = lean_ctor_get(v___x_494_, 1);
v___x_497_ = lean_unbox_usize(v_key_495_);
v___x_498_ = lean_usize_dec_eq(v_x_487_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
v___x_499_ = lean_box(0);
return v___x_499_;
}
else
{
lean_object* v___x_500_; 
lean_inc(v_val_496_);
v___x_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_500_, 0, v_val_496_);
return v___x_500_;
}
}
case 1:
{
lean_object* v_node_501_; size_t v___x_502_; 
v_node_501_ = lean_ctor_get(v___x_494_, 0);
v___x_502_ = lean_usize_shift_right(v_x_486_, v___x_490_);
v_x_485_ = v_node_501_;
v_x_486_ = v___x_502_;
goto _start;
}
default: 
{
lean_object* v___x_504_; 
v___x_504_ = lean_box(0);
return v___x_504_;
}
}
}
else
{
lean_object* v_ks_505_; lean_object* v_vs_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v_ks_505_ = lean_ctor_get(v_x_485_, 0);
v_vs_506_ = lean_ctor_get(v_x_485_, 1);
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(v_ks_505_, v_vs_506_, v___x_507_, v_x_487_);
return v___x_508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg___boxed(lean_object* v_x_509_, lean_object* v_x_510_, lean_object* v_x_511_){
_start:
{
size_t v_x_1902__boxed_512_; size_t v_x_1903__boxed_513_; lean_object* v_res_514_; 
v_x_1902__boxed_512_ = lean_unbox_usize(v_x_510_);
lean_dec(v_x_510_);
v_x_1903__boxed_513_ = lean_unbox_usize(v_x_511_);
lean_dec(v_x_511_);
v_res_514_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_509_, v_x_1902__boxed_512_, v_x_1903__boxed_513_);
lean_dec_ref(v_x_509_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(lean_object* v_x_515_, size_t v_x_516_){
_start:
{
uint64_t v___x_517_; size_t v___x_518_; lean_object* v___x_519_; 
v___x_517_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_516_);
v___x_518_ = lean_uint64_to_usize(v___x_517_);
v___x_519_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_515_, v___x_518_, v_x_516_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg___boxed(lean_object* v_x_520_, lean_object* v_x_521_){
_start:
{
size_t v_x_1953__boxed_522_; lean_object* v_res_523_; 
v_x_1953__boxed_522_ = lean_unbox_usize(v_x_521_);
lean_dec(v_x_521_);
v_res_523_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(v_x_520_, v_x_1953__boxed_522_);
lean_dec_ref(v_x_520_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(lean_object* v_xs_524_, size_t v_v_525_, lean_object* v_i_526_){
_start:
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = lean_array_get_size(v_xs_524_);
v___x_528_ = lean_nat_dec_lt(v_i_526_, v___x_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; 
lean_dec(v_i_526_);
v___x_529_ = lean_box(0);
return v___x_529_;
}
else
{
lean_object* v___x_530_; size_t v___x_531_; uint8_t v___x_532_; 
v___x_530_ = lean_array_fget_borrowed(v_xs_524_, v_i_526_);
v___x_531_ = lean_unbox_usize(v___x_530_);
v___x_532_ = lean_usize_dec_eq(v___x_531_, v_v_525_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = lean_nat_add(v_i_526_, v___x_533_);
lean_dec(v_i_526_);
v_i_526_ = v___x_534_;
goto _start;
}
else
{
lean_object* v___x_536_; 
v___x_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_536_, 0, v_i_526_);
return v___x_536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14___boxed(lean_object* v_xs_537_, lean_object* v_v_538_, lean_object* v_i_539_){
_start:
{
size_t v_v_boxed_540_; lean_object* v_res_541_; 
v_v_boxed_540_ = lean_unbox_usize(v_v_538_);
lean_dec(v_v_538_);
v_res_541_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(v_xs_537_, v_v_boxed_540_, v_i_539_);
lean_dec_ref(v_xs_537_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(lean_object* v_xs_542_, size_t v_v_543_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(v_xs_542_, v_v_543_, v___x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11___boxed(lean_object* v_xs_546_, lean_object* v_v_547_){
_start:
{
size_t v_v_boxed_548_; lean_object* v_res_549_; 
v_v_boxed_548_ = lean_unbox_usize(v_v_547_);
lean_dec(v_v_547_);
v_res_549_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(v_xs_546_, v_v_boxed_548_);
lean_dec_ref(v_xs_546_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(lean_object* v_x_550_, size_t v_x_551_, size_t v_x_552_){
_start:
{
if (lean_obj_tag(v_x_550_) == 0)
{
lean_object* v_es_553_; lean_object* v___x_554_; size_t v___x_555_; size_t v___x_556_; size_t v___x_557_; lean_object* v_j_558_; lean_object* v_entry_559_; 
v_es_553_ = lean_ctor_get(v_x_550_, 0);
v___x_554_ = lean_box(2);
v___x_555_ = ((size_t)5ULL);
v___x_556_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1);
v___x_557_ = lean_usize_land(v_x_551_, v___x_556_);
v_j_558_ = lean_usize_to_nat(v___x_557_);
v_entry_559_ = lean_array_get(v___x_554_, v_es_553_, v_j_558_);
switch(lean_obj_tag(v_entry_559_))
{
case 0:
{
lean_object* v_key_560_; size_t v___x_561_; uint8_t v___x_562_; 
v_key_560_ = lean_ctor_get(v_entry_559_, 0);
lean_inc(v_key_560_);
lean_dec_ref(v_entry_559_);
v___x_561_ = lean_unbox_usize(v_key_560_);
lean_dec(v_key_560_);
v___x_562_ = lean_usize_dec_eq(v_x_552_, v___x_561_);
if (v___x_562_ == 0)
{
lean_dec(v_j_558_);
return v_x_550_;
}
else
{
lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_570_; 
lean_inc_ref(v_es_553_);
v_isSharedCheck_570_ = !lean_is_exclusive(v_x_550_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; 
v_unused_571_ = lean_ctor_get(v_x_550_, 0);
lean_dec(v_unused_571_);
v___x_564_ = v_x_550_;
v_isShared_565_ = v_isSharedCheck_570_;
goto v_resetjp_563_;
}
else
{
lean_dec(v_x_550_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_570_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_566_ = lean_array_set(v_es_553_, v_j_558_, v___x_554_);
lean_dec(v_j_558_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_566_);
v___x_568_ = v___x_564_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
case 1:
{
lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_605_; 
lean_inc_ref(v_es_553_);
v_isSharedCheck_605_ = !lean_is_exclusive(v_x_550_);
if (v_isSharedCheck_605_ == 0)
{
lean_object* v_unused_606_; 
v_unused_606_ = lean_ctor_get(v_x_550_, 0);
lean_dec(v_unused_606_);
v___x_573_ = v_x_550_;
v_isShared_574_ = v_isSharedCheck_605_;
goto v_resetjp_572_;
}
else
{
lean_dec(v_x_550_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_605_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v_node_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_604_; 
v_node_575_ = lean_ctor_get(v_entry_559_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v_entry_559_);
if (v_isSharedCheck_604_ == 0)
{
v___x_577_ = v_entry_559_;
v_isShared_578_ = v_isSharedCheck_604_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_node_575_);
lean_dec(v_entry_559_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_604_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v_entries_579_; size_t v___x_580_; lean_object* v_newNode_581_; lean_object* v___x_582_; 
v_entries_579_ = lean_array_set(v_es_553_, v_j_558_, v___x_554_);
v___x_580_ = lean_usize_shift_right(v_x_551_, v___x_555_);
v_newNode_581_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_node_575_, v___x_580_, v_x_552_);
lean_inc_ref(v_newNode_581_);
v___x_582_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_581_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v___x_584_; 
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v_newNode_581_);
v___x_584_ = v___x_577_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_newNode_581_);
v___x_584_ = v_reuseFailAlloc_589_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_585_ = lean_array_set(v_entries_579_, v_j_558_, v___x_584_);
lean_dec(v_j_558_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_585_);
v___x_587_ = v___x_573_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
else
{
lean_object* v_val_590_; lean_object* v_fst_591_; lean_object* v_snd_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_603_; 
lean_dec_ref(v_newNode_581_);
lean_del_object(v___x_577_);
v_val_590_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_val_590_);
lean_dec_ref(v___x_582_);
v_fst_591_ = lean_ctor_get(v_val_590_, 0);
v_snd_592_ = lean_ctor_get(v_val_590_, 1);
v_isSharedCheck_603_ = !lean_is_exclusive(v_val_590_);
if (v_isSharedCheck_603_ == 0)
{
v___x_594_ = v_val_590_;
v_isShared_595_ = v_isSharedCheck_603_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_snd_592_);
lean_inc(v_fst_591_);
lean_dec(v_val_590_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_603_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_fst_591_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_snd_592_);
v___x_597_ = v_reuseFailAlloc_602_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = lean_array_set(v_entries_579_, v_j_558_, v___x_597_);
lean_dec(v_j_558_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_598_);
v___x_600_ = v___x_573_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_558_);
return v_x_550_;
}
}
}
else
{
lean_object* v_ks_607_; lean_object* v_vs_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_622_; 
v_ks_607_ = lean_ctor_get(v_x_550_, 0);
v_vs_608_ = lean_ctor_get(v_x_550_, 1);
v_isSharedCheck_622_ = !lean_is_exclusive(v_x_550_);
if (v_isSharedCheck_622_ == 0)
{
v___x_610_ = v_x_550_;
v_isShared_611_ = v_isSharedCheck_622_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_vs_608_);
lean_inc(v_ks_607_);
lean_dec(v_x_550_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_622_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; 
v___x_612_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(v_ks_607_, v_x_552_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v___x_614_; 
if (v_isShared_611_ == 0)
{
v___x_614_ = v___x_610_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_ks_607_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_vs_608_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
else
{
lean_object* v_val_616_; lean_object* v_keys_x27_617_; lean_object* v_vals_x27_618_; lean_object* v___x_620_; 
v_val_616_ = lean_ctor_get(v___x_612_, 0);
lean_inc_n(v_val_616_, 2);
lean_dec_ref(v___x_612_);
v_keys_x27_617_ = l_Array_eraseIdx___redArg(v_ks_607_, v_val_616_);
v_vals_x27_618_ = l_Array_eraseIdx___redArg(v_vs_608_, v_val_616_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 1, v_vals_x27_618_);
lean_ctor_set(v___x_610_, 0, v_keys_x27_617_);
v___x_620_ = v___x_610_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_keys_x27_617_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_vals_x27_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg___boxed(lean_object* v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
size_t v_x_1995__boxed_626_; size_t v_x_1996__boxed_627_; lean_object* v_res_628_; 
v_x_1995__boxed_626_ = lean_unbox_usize(v_x_624_);
lean_dec(v_x_624_);
v_x_1996__boxed_627_ = lean_unbox_usize(v_x_625_);
lean_dec(v_x_625_);
v_res_628_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_623_, v_x_1995__boxed_626_, v_x_1996__boxed_627_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(lean_object* v_x_629_, size_t v_x_630_){
_start:
{
uint64_t v___x_631_; size_t v_h_632_; lean_object* v___x_633_; 
v___x_631_ = lean_usize_to_uint64(v_x_630_);
v_h_632_ = lean_uint64_to_usize(v___x_631_);
v___x_633_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_629_, v_h_632_, v_x_630_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg___boxed(lean_object* v_x_634_, lean_object* v_x_635_){
_start:
{
size_t v_x_2135__boxed_636_; lean_object* v_res_637_; 
v_x_2135__boxed_636_ = lean_unbox_usize(v_x_635_);
lean_dec(v_x_635_);
v_res_637_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(v_x_634_, v_x_2135__boxed_636_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_x_638_, lean_object* v_x_639_, size_t v_x_640_, lean_object* v_x_641_){
_start:
{
lean_object* v_ks_642_; lean_object* v_vs_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_670_; 
v_ks_642_ = lean_ctor_get(v_x_638_, 0);
v_vs_643_ = lean_ctor_get(v_x_638_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v_x_638_);
if (v_isSharedCheck_670_ == 0)
{
v___x_645_ = v_x_638_;
v_isShared_646_ = v_isSharedCheck_670_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_vs_643_);
lean_inc(v_ks_642_);
lean_dec(v_x_638_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_670_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_array_get_size(v_ks_642_);
v___x_648_ = lean_nat_dec_lt(v_x_639_, v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_653_; 
lean_dec(v_x_639_);
v___x_649_ = lean_box_usize(v_x_640_);
v___x_650_ = lean_array_push(v_ks_642_, v___x_649_);
v___x_651_ = lean_array_push(v_vs_643_, v_x_641_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 1, v___x_651_);
lean_ctor_set(v___x_645_, 0, v___x_650_);
v___x_653_ = v___x_645_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_650_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v___x_651_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
else
{
lean_object* v_k_x27_655_; size_t v___x_656_; uint8_t v___x_657_; 
v_k_x27_655_ = lean_array_fget_borrowed(v_ks_642_, v_x_639_);
v___x_656_ = lean_unbox_usize(v_k_x27_655_);
v___x_657_ = lean_usize_dec_eq(v_x_640_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_659_; 
if (v_isShared_646_ == 0)
{
v___x_659_ = v___x_645_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_ks_642_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_vs_643_);
v___x_659_ = v_reuseFailAlloc_663_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_unsigned_to_nat(1u);
v___x_661_ = lean_nat_add(v_x_639_, v___x_660_);
lean_dec(v_x_639_);
v_x_638_ = v___x_659_;
v_x_639_ = v___x_661_;
goto _start;
}
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_664_ = lean_box_usize(v_x_640_);
v___x_665_ = lean_array_fset(v_ks_642_, v_x_639_, v___x_664_);
v___x_666_ = lean_array_fset(v_vs_643_, v_x_639_, v_x_641_);
lean_dec(v_x_639_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 1, v___x_666_);
lean_ctor_set(v___x_645_, 0, v___x_665_);
v___x_668_ = v___x_645_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_x_671_, lean_object* v_x_672_, lean_object* v_x_673_, lean_object* v_x_674_){
_start:
{
size_t v_x_2146__boxed_675_; lean_object* v_res_676_; 
v_x_2146__boxed_675_ = lean_unbox_usize(v_x_673_);
lean_dec(v_x_673_);
v_res_676_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_x_671_, v_x_672_, v_x_2146__boxed_675_, v_x_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(lean_object* v_n_677_, size_t v_k_678_, lean_object* v_v_679_){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_n_677_, v___x_680_, v_k_678_, v_v_679_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_n_682_, lean_object* v_k_683_, lean_object* v_v_684_){
_start:
{
size_t v_k_boxed_685_; lean_object* v_res_686_; 
v_k_boxed_685_ = lean_unbox_usize(v_k_683_);
lean_dec(v_k_683_);
v_res_686_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v_n_682_, v_k_boxed_685_, v_v_684_);
return v_res_686_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(lean_object* v_x_688_, size_t v_x_689_, size_t v_x_690_, size_t v_x_691_, lean_object* v_x_692_){
_start:
{
if (lean_obj_tag(v_x_688_) == 0)
{
lean_object* v_es_693_; size_t v___x_694_; size_t v___x_695_; size_t v___x_696_; size_t v___x_697_; lean_object* v_j_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v_es_693_ = lean_ctor_get(v_x_688_, 0);
v___x_694_ = ((size_t)5ULL);
v___x_695_ = ((size_t)1ULL);
v___x_696_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1);
v___x_697_ = lean_usize_land(v_x_689_, v___x_696_);
v_j_698_ = lean_usize_to_nat(v___x_697_);
v___x_699_ = lean_array_get_size(v_es_693_);
v___x_700_ = lean_nat_dec_lt(v_j_698_, v___x_699_);
if (v___x_700_ == 0)
{
lean_dec(v_j_698_);
lean_dec(v_x_692_);
return v_x_688_;
}
else
{
lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_741_; 
lean_inc_ref(v_es_693_);
v_isSharedCheck_741_ = !lean_is_exclusive(v_x_688_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; 
v_unused_742_ = lean_ctor_get(v_x_688_, 0);
lean_dec(v_unused_742_);
v___x_702_ = v_x_688_;
v_isShared_703_ = v_isSharedCheck_741_;
goto v_resetjp_701_;
}
else
{
lean_dec(v_x_688_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_741_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v_v_704_; lean_object* v___x_705_; lean_object* v_xs_x27_706_; lean_object* v___y_708_; 
v_v_704_ = lean_array_fget(v_es_693_, v_j_698_);
v___x_705_ = lean_box(0);
v_xs_x27_706_ = lean_array_fset(v_es_693_, v_j_698_, v___x_705_);
switch(lean_obj_tag(v_v_704_))
{
case 0:
{
lean_object* v_key_713_; lean_object* v_val_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_727_; 
v_key_713_ = lean_ctor_get(v_v_704_, 0);
v_val_714_ = lean_ctor_get(v_v_704_, 1);
v_isSharedCheck_727_ = !lean_is_exclusive(v_v_704_);
if (v_isSharedCheck_727_ == 0)
{
v___x_716_ = v_v_704_;
v_isShared_717_ = v_isSharedCheck_727_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_val_714_);
lean_inc(v_key_713_);
lean_dec(v_v_704_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_727_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
size_t v___x_718_; uint8_t v___x_719_; 
v___x_718_ = lean_unbox_usize(v_key_713_);
v___x_719_ = lean_usize_dec_eq(v_x_691_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
lean_del_object(v___x_716_);
v___x_720_ = lean_box_usize(v_x_691_);
v___x_721_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_713_, v_val_714_, v___x_720_, v_x_692_);
v___x_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
v___y_708_ = v___x_722_;
goto v___jp_707_;
}
else
{
lean_object* v___x_723_; lean_object* v___x_725_; 
lean_dec(v_val_714_);
lean_dec(v_key_713_);
v___x_723_ = lean_box_usize(v_x_691_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 1, v_x_692_);
lean_ctor_set(v___x_716_, 0, v___x_723_);
v___x_725_ = v___x_716_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_x_692_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
v___y_708_ = v___x_725_;
goto v___jp_707_;
}
}
}
}
case 1:
{
lean_object* v_node_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_738_; 
v_node_728_ = lean_ctor_get(v_v_704_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v_v_704_);
if (v_isSharedCheck_738_ == 0)
{
v___x_730_ = v_v_704_;
v_isShared_731_ = v_isSharedCheck_738_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_node_728_);
lean_dec(v_v_704_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_738_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
size_t v___x_732_; size_t v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_732_ = lean_usize_shift_right(v_x_689_, v___x_694_);
v___x_733_ = lean_usize_add(v_x_690_, v___x_695_);
v___x_734_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_node_728_, v___x_732_, v___x_733_, v_x_691_, v_x_692_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_734_);
v___x_736_ = v___x_730_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
v___y_708_ = v___x_736_;
goto v___jp_707_;
}
}
}
default: 
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_box_usize(v_x_691_);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
lean_ctor_set(v___x_740_, 1, v_x_692_);
v___y_708_ = v___x_740_;
goto v___jp_707_;
}
}
v___jp_707_:
{
lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_709_ = lean_array_fset(v_xs_x27_706_, v_j_698_, v___y_708_);
lean_dec(v_j_698_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_709_);
v___x_711_ = v___x_702_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
else
{
lean_object* v_ks_743_; lean_object* v_vs_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_764_; 
v_ks_743_ = lean_ctor_get(v_x_688_, 0);
v_vs_744_ = lean_ctor_get(v_x_688_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v_x_688_);
if (v_isSharedCheck_764_ == 0)
{
v___x_746_ = v_x_688_;
v_isShared_747_ = v_isSharedCheck_764_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_vs_744_);
lean_inc(v_ks_743_);
lean_dec(v_x_688_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_764_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_ks_743_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_vs_744_);
v___x_749_ = v_reuseFailAlloc_763_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v_newNode_750_; uint8_t v___y_752_; size_t v___x_758_; uint8_t v___x_759_; 
v_newNode_750_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v___x_749_, v_x_691_, v_x_692_);
v___x_758_ = ((size_t)7ULL);
v___x_759_ = lean_usize_dec_le(v___x_758_, v_x_690_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_760_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_750_);
v___x_761_ = lean_unsigned_to_nat(4u);
v___x_762_ = lean_nat_dec_lt(v___x_760_, v___x_761_);
lean_dec(v___x_760_);
v___y_752_ = v___x_762_;
goto v___jp_751_;
}
else
{
v___y_752_ = v___x_759_;
goto v___jp_751_;
}
v___jp_751_:
{
if (v___y_752_ == 0)
{
lean_object* v_ks_753_; lean_object* v_vs_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v_ks_753_ = lean_ctor_get(v_newNode_750_, 0);
lean_inc_ref(v_ks_753_);
v_vs_754_ = lean_ctor_get(v_newNode_750_, 1);
lean_inc_ref(v_vs_754_);
lean_dec_ref(v_newNode_750_);
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0);
v___x_757_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_x_690_, v_ks_753_, v_vs_754_, v___x_755_, v___x_756_);
lean_dec_ref(v_vs_754_);
lean_dec_ref(v_ks_753_);
return v___x_757_;
}
else
{
return v_newNode_750_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(size_t v_depth_765_, lean_object* v_keys_766_, lean_object* v_vals_767_, lean_object* v_i_768_, lean_object* v_entries_769_){
_start:
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = lean_array_get_size(v_keys_766_);
v___x_771_ = lean_nat_dec_lt(v_i_768_, v___x_770_);
if (v___x_771_ == 0)
{
lean_dec(v_i_768_);
return v_entries_769_;
}
else
{
lean_object* v_k_772_; lean_object* v_v_773_; size_t v___x_774_; uint64_t v___x_775_; size_t v_h_776_; size_t v___x_777_; lean_object* v___x_778_; size_t v___x_779_; size_t v___x_780_; size_t v___x_781_; size_t v_h_782_; lean_object* v___x_783_; size_t v___x_784_; lean_object* v___x_785_; 
v_k_772_ = lean_array_fget_borrowed(v_keys_766_, v_i_768_);
v_v_773_ = lean_array_fget_borrowed(v_vals_767_, v_i_768_);
v___x_774_ = lean_unbox_usize(v_k_772_);
v___x_775_ = l_Lean_Lsp_instHashableRpcRef_hash(v___x_774_);
v_h_776_ = lean_uint64_to_usize(v___x_775_);
v___x_777_ = ((size_t)5ULL);
v___x_778_ = lean_unsigned_to_nat(1u);
v___x_779_ = ((size_t)1ULL);
v___x_780_ = lean_usize_sub(v_depth_765_, v___x_779_);
v___x_781_ = lean_usize_mul(v___x_777_, v___x_780_);
v_h_782_ = lean_usize_shift_right(v_h_776_, v___x_781_);
v___x_783_ = lean_nat_add(v_i_768_, v___x_778_);
lean_dec(v_i_768_);
v___x_784_ = lean_unbox_usize(v_k_772_);
lean_inc(v_v_773_);
v___x_785_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_entries_769_, v_h_782_, v_depth_765_, v___x_784_, v_v_773_);
v_i_768_ = v___x_783_;
v_entries_769_ = v___x_785_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_787_, lean_object* v_keys_788_, lean_object* v_vals_789_, lean_object* v_i_790_, lean_object* v_entries_791_){
_start:
{
size_t v_depth_boxed_792_; lean_object* v_res_793_; 
v_depth_boxed_792_ = lean_unbox_usize(v_depth_787_);
lean_dec(v_depth_787_);
v_res_793_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_depth_boxed_792_, v_keys_788_, v_vals_789_, v_i_790_, v_entries_791_);
lean_dec_ref(v_vals_789_);
lean_dec_ref(v_keys_788_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___boxed(lean_object* v_x_794_, lean_object* v_x_795_, lean_object* v_x_796_, lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
size_t v_x_2237__boxed_799_; size_t v_x_2238__boxed_800_; size_t v_x_2239__boxed_801_; lean_object* v_res_802_; 
v_x_2237__boxed_799_ = lean_unbox_usize(v_x_795_);
lean_dec(v_x_795_);
v_x_2238__boxed_800_ = lean_unbox_usize(v_x_796_);
lean_dec(v_x_796_);
v_x_2239__boxed_801_ = lean_unbox_usize(v_x_797_);
lean_dec(v_x_797_);
v_res_802_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_794_, v_x_2237__boxed_799_, v_x_2238__boxed_800_, v_x_2239__boxed_801_, v_x_798_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(lean_object* v_x_803_, size_t v_x_804_, lean_object* v_x_805_){
_start:
{
uint64_t v___x_806_; size_t v___x_807_; size_t v___x_808_; lean_object* v___x_809_; 
v___x_806_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_804_);
v___x_807_ = lean_uint64_to_usize(v___x_806_);
v___x_808_ = ((size_t)1ULL);
v___x_809_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_803_, v___x_807_, v___x_808_, v_x_804_, v_x_805_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg___boxed(lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_){
_start:
{
size_t v_x_2405__boxed_813_; lean_object* v_res_814_; 
v_x_2405__boxed_813_ = lean_unbox_usize(v_x_811_);
lean_dec(v_x_811_);
v_res_814_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(v_x_810_, v_x_2405__boxed_813_, v_x_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcReleaseRef(size_t v_r_815_, lean_object* v_a_816_){
_start:
{
lean_object* v___y_818_; lean_object* v_aliveRefs_822_; lean_object* v_refsById_823_; size_t v_nextRef_824_; uint8_t v_wireFormat_825_; lean_object* v___x_826_; 
v_aliveRefs_822_ = lean_ctor_get(v_a_816_, 0);
v_refsById_823_ = lean_ctor_get(v_a_816_, 1);
v_nextRef_824_ = lean_ctor_get_usize(v_a_816_, 2);
v_wireFormat_825_ = lean_ctor_get_uint8(v_a_816_, sizeof(void*)*3);
v___x_826_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(v_aliveRefs_822_, v_r_815_);
if (lean_obj_tag(v___x_826_) == 1)
{
lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_854_; 
lean_inc_ref(v_refsById_823_);
lean_inc_ref(v_aliveRefs_822_);
v_isSharedCheck_854_ = !lean_is_exclusive(v_a_816_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; lean_object* v_unused_856_; 
v_unused_855_ = lean_ctor_get(v_a_816_, 1);
lean_dec(v_unused_855_);
v_unused_856_ = lean_ctor_get(v_a_816_, 0);
lean_dec(v_unused_856_);
v___x_828_ = v_a_816_;
v_isShared_829_ = v_isSharedCheck_854_;
goto v_resetjp_827_;
}
else
{
lean_dec(v_a_816_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_854_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v_val_830_; lean_object* v_obj_831_; size_t v_id_832_; lean_object* v_rc_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_853_; 
v_val_830_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_val_830_);
lean_dec_ref(v___x_826_);
v_obj_831_ = lean_ctor_get(v_val_830_, 0);
v_id_832_ = lean_ctor_get_usize(v_val_830_, 2);
v_rc_833_ = lean_ctor_get(v_val_830_, 1);
v_isSharedCheck_853_ = !lean_is_exclusive(v_val_830_);
if (v_isSharedCheck_853_ == 0)
{
v___x_835_ = v_val_830_;
v_isShared_836_ = v_isSharedCheck_853_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_rc_833_);
lean_inc(v_obj_831_);
lean_dec(v_val_830_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_853_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_837_ = lean_unsigned_to_nat(1u);
v___x_838_ = lean_nat_sub(v_rc_833_, v___x_837_);
lean_dec(v_rc_833_);
v___x_839_ = lean_unsigned_to_nat(0u);
v___x_840_ = lean_nat_dec_eq(v___x_838_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_842_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v___x_838_);
v___x_842_ = v___x_835_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_obj_831_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_838_);
lean_ctor_set_usize(v_reuseFailAlloc_847_, 2, v_id_832_);
v___x_842_ = v_reuseFailAlloc_847_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(v_aliveRefs_822_, v_r_815_, v___x_842_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v___x_843_);
v___x_845_ = v___x_828_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_refsById_823_);
lean_ctor_set_usize(v_reuseFailAlloc_846_, 2, v_nextRef_824_);
lean_ctor_set_uint8(v_reuseFailAlloc_846_, sizeof(void*)*3, v_wireFormat_825_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
v___y_818_ = v___x_845_;
goto v___jp_817_;
}
}
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
lean_dec(v___x_838_);
lean_del_object(v___x_835_);
lean_dec(v_obj_831_);
v___x_848_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(v_aliveRefs_822_, v_r_815_);
v___x_849_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(v_refsById_823_, v_id_832_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v___x_849_);
lean_ctor_set(v___x_828_, 0, v___x_848_);
v___x_851_ = v___x_828_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v___x_849_);
lean_ctor_set_usize(v_reuseFailAlloc_852_, 2, v_nextRef_824_);
lean_ctor_set_uint8(v_reuseFailAlloc_852_, sizeof(void*)*3, v_wireFormat_825_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
v___y_818_ = v___x_851_;
goto v___jp_817_;
}
}
}
}
}
else
{
uint8_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec(v___x_826_);
v___x_857_ = 0;
v___x_858_ = lean_box(v___x_857_);
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set(v___x_859_, 1, v_a_816_);
return v___x_859_;
}
v___jp_817_:
{
uint8_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_819_ = 1;
v___x_820_ = lean_box(v___x_819_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v___y_818_);
return v___x_821_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcReleaseRef___boxed(lean_object* v_r_860_, lean_object* v_a_861_){
_start:
{
size_t v_r_boxed_862_; lean_object* v_res_863_; 
v_r_boxed_862_ = lean_unbox_usize(v_r_860_);
lean_dec(v_r_860_);
v_res_863_ = l_Lean_Server_rpcReleaseRef(v_r_boxed_862_, v_a_861_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0(lean_object* v_00_u03b2_864_, lean_object* v_x_865_, size_t v_x_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(v_x_865_, v_x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___boxed(lean_object* v_00_u03b2_868_, lean_object* v_x_869_, lean_object* v_x_870_){
_start:
{
size_t v_x_2497__boxed_871_; lean_object* v_res_872_; 
v_x_2497__boxed_871_ = lean_unbox_usize(v_x_870_);
lean_dec(v_x_870_);
v_res_872_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0(v_00_u03b2_868_, v_x_869_, v_x_2497__boxed_871_);
lean_dec_ref(v_x_869_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1(lean_object* v_00_u03b2_873_, lean_object* v_x_874_, size_t v_x_875_, lean_object* v_x_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(v_x_874_, v_x_875_, v_x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___boxed(lean_object* v_00_u03b2_878_, lean_object* v_x_879_, lean_object* v_x_880_, lean_object* v_x_881_){
_start:
{
size_t v_x_2505__boxed_882_; lean_object* v_res_883_; 
v_x_2505__boxed_882_ = lean_unbox_usize(v_x_880_);
lean_dec(v_x_880_);
v_res_883_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1(v_00_u03b2_878_, v_x_879_, v_x_2505__boxed_882_, v_x_881_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2(lean_object* v_00_u03b2_884_, lean_object* v_x_885_, size_t v_x_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(v_x_885_, v_x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___boxed(lean_object* v_00_u03b2_888_, lean_object* v_x_889_, lean_object* v_x_890_){
_start:
{
size_t v_x_2516__boxed_891_; lean_object* v_res_892_; 
v_x_2516__boxed_891_ = lean_unbox_usize(v_x_890_);
lean_dec(v_x_890_);
v_res_892_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2(v_00_u03b2_888_, v_x_889_, v_x_2516__boxed_891_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3(lean_object* v_00_u03b2_893_, lean_object* v_x_894_, size_t v_x_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(v_x_894_, v_x_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___boxed(lean_object* v_00_u03b2_897_, lean_object* v_x_898_, lean_object* v_x_899_){
_start:
{
size_t v_x_2524__boxed_900_; lean_object* v_res_901_; 
v_x_2524__boxed_900_ = lean_unbox_usize(v_x_899_);
lean_dec(v_x_899_);
v_res_901_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3(v_00_u03b2_897_, v_x_898_, v_x_2524__boxed_900_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0(lean_object* v_00_u03b2_902_, lean_object* v_x_903_, size_t v_x_904_, size_t v_x_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_903_, v_x_904_, v_x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___boxed(lean_object* v_00_u03b2_907_, lean_object* v_x_908_, lean_object* v_x_909_, lean_object* v_x_910_){
_start:
{
size_t v_x_2532__boxed_911_; size_t v_x_2533__boxed_912_; lean_object* v_res_913_; 
v_x_2532__boxed_911_ = lean_unbox_usize(v_x_909_);
lean_dec(v_x_909_);
v_x_2533__boxed_912_ = lean_unbox_usize(v_x_910_);
lean_dec(v_x_910_);
v_res_913_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0(v_00_u03b2_907_, v_x_908_, v_x_2532__boxed_911_, v_x_2533__boxed_912_);
lean_dec_ref(v_x_908_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2(lean_object* v_00_u03b2_914_, lean_object* v_x_915_, size_t v_x_916_, size_t v_x_917_, size_t v_x_918_, lean_object* v_x_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_915_, v_x_916_, v_x_917_, v_x_918_, v_x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___boxed(lean_object* v_00_u03b2_921_, lean_object* v_x_922_, lean_object* v_x_923_, lean_object* v_x_924_, lean_object* v_x_925_, lean_object* v_x_926_){
_start:
{
size_t v_x_2543__boxed_927_; size_t v_x_2544__boxed_928_; size_t v_x_2545__boxed_929_; lean_object* v_res_930_; 
v_x_2543__boxed_927_ = lean_unbox_usize(v_x_923_);
lean_dec(v_x_923_);
v_x_2544__boxed_928_ = lean_unbox_usize(v_x_924_);
lean_dec(v_x_924_);
v_x_2545__boxed_929_ = lean_unbox_usize(v_x_925_);
lean_dec(v_x_925_);
v_res_930_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2(v_00_u03b2_921_, v_x_922_, v_x_2543__boxed_927_, v_x_2544__boxed_928_, v_x_2545__boxed_929_, v_x_926_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4(lean_object* v_00_u03b2_931_, lean_object* v_x_932_, size_t v_x_933_, size_t v_x_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_x_932_, v_x_933_, v_x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___boxed(lean_object* v_00_u03b2_936_, lean_object* v_x_937_, lean_object* v_x_938_, lean_object* v_x_939_){
_start:
{
size_t v_x_2560__boxed_940_; size_t v_x_2561__boxed_941_; lean_object* v_res_942_; 
v_x_2560__boxed_940_ = lean_unbox_usize(v_x_938_);
lean_dec(v_x_938_);
v_x_2561__boxed_941_ = lean_unbox_usize(v_x_939_);
lean_dec(v_x_939_);
v_res_942_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4(v_00_u03b2_936_, v_x_937_, v_x_2560__boxed_940_, v_x_2561__boxed_941_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6(lean_object* v_00_u03b2_943_, lean_object* v_x_944_, size_t v_x_945_, size_t v_x_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_944_, v_x_945_, v_x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___boxed(lean_object* v_00_u03b2_948_, lean_object* v_x_949_, lean_object* v_x_950_, lean_object* v_x_951_){
_start:
{
size_t v_x_2571__boxed_952_; size_t v_x_2572__boxed_953_; lean_object* v_res_954_; 
v_x_2571__boxed_952_ = lean_unbox_usize(v_x_950_);
lean_dec(v_x_950_);
v_x_2572__boxed_953_ = lean_unbox_usize(v_x_951_);
lean_dec(v_x_951_);
v_res_954_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6(v_00_u03b2_948_, v_x_949_, v_x_2571__boxed_952_, v_x_2572__boxed_953_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_955_, lean_object* v_keys_956_, lean_object* v_vals_957_, lean_object* v_heq_958_, lean_object* v_i_959_, size_t v_k_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(v_keys_956_, v_vals_957_, v_i_959_, v_k_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_962_, lean_object* v_keys_963_, lean_object* v_vals_964_, lean_object* v_heq_965_, lean_object* v_i_966_, lean_object* v_k_967_){
_start:
{
size_t v_k_boxed_968_; lean_object* v_res_969_; 
v_k_boxed_968_ = lean_unbox_usize(v_k_967_);
lean_dec(v_k_967_);
v_res_969_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1(v_00_u03b2_962_, v_keys_963_, v_vals_964_, v_heq_965_, v_i_966_, v_k_boxed_968_);
lean_dec_ref(v_vals_964_);
lean_dec_ref(v_keys_963_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_970_, lean_object* v_n_971_, size_t v_k_972_, lean_object* v_v_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v_n_971_, v_k_972_, v_v_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_975_, lean_object* v_n_976_, lean_object* v_k_977_, lean_object* v_v_978_){
_start:
{
size_t v_k_boxed_979_; lean_object* v_res_980_; 
v_k_boxed_979_ = lean_unbox_usize(v_k_977_);
lean_dec(v_k_977_);
v_res_980_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4(v_00_u03b2_975_, v_n_976_, v_k_boxed_979_, v_v_978_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_981_, size_t v_depth_982_, lean_object* v_keys_983_, lean_object* v_vals_984_, lean_object* v_heq_985_, lean_object* v_i_986_, lean_object* v_entries_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_depth_982_, v_keys_983_, v_vals_984_, v_i_986_, v_entries_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_989_, lean_object* v_depth_990_, lean_object* v_keys_991_, lean_object* v_vals_992_, lean_object* v_heq_993_, lean_object* v_i_994_, lean_object* v_entries_995_){
_start:
{
size_t v_depth_boxed_996_; lean_object* v_res_997_; 
v_depth_boxed_996_ = lean_unbox_usize(v_depth_990_);
lean_dec(v_depth_990_);
v_res_997_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5(v_00_u03b2_989_, v_depth_boxed_996_, v_keys_991_, v_vals_992_, v_heq_993_, v_i_994_, v_entries_995_);
lean_dec_ref(v_vals_992_);
lean_dec_ref(v_keys_991_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_998_, lean_object* v_x_999_, lean_object* v_x_1000_, size_t v_x_1001_, lean_object* v_x_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_x_999_, v_x_1000_, v_x_1001_, v_x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1004_, lean_object* v_x_1005_, lean_object* v_x_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_){
_start:
{
size_t v_x_2589__boxed_1009_; lean_object* v_res_1010_; 
v_x_2589__boxed_1009_ = lean_unbox_usize(v_x_1007_);
lean_dec(v_x_1007_);
v_res_1010_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7(v_00_u03b2_1004_, v_x_1005_, v_x_1006_, v_x_2589__boxed_1009_, v_x_1008_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__0(lean_object* v_inst_1011_, lean_object* v_a_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = lean_apply_1(v_inst_1011_, v_a_1012_);
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
lean_ctor_set(v___x_1015_, 1, v___y_1013_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1(lean_object* v_inst_1016_, lean_object* v___x_1017_, lean_object* v___x_1018_, lean_object* v_j_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_201__overap_1022_; lean_object* v___x_1023_; 
v___x_1021_ = lean_apply_1(v_inst_1016_, v_j_1019_);
v___x_201__overap_1022_ = l_MonadExcept_ofExcept___redArg(v___x_1017_, v___x_1018_, v___x_1021_);
lean_inc_ref(v___y_1020_);
v___x_1023_ = lean_apply_1(v___x_201__overap_1022_, v___y_1020_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1___boxed(lean_object* v_inst_1024_, lean_object* v___x_1025_, lean_object* v___x_1026_, lean_object* v_j_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1(v_inst_1024_, v___x_1025_, v___x_1026_, v_j_1027_, v___y_1028_);
lean_dec_ref(v___y_1028_);
return v_res_1029_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9));
v___x_1050_ = l_ReaderT_instMonad___redArg(v___x_1049_);
return v___x_1050_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___f_1052_; 
v___x_1051_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___f_1052_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1052_, 0, v___x_1051_);
return v___f_1052_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___f_1054_; 
v___x_1053_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___f_1054_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_1054_, 0, v___x_1053_);
return v___f_1054_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___f_1056_; 
v___x_1055_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___f_1056_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_1056_, 0, v___x_1055_);
return v___f_1056_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___f_1058_; 
v___x_1057_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___f_1058_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_1058_, 0, v___x_1057_);
return v___f_1058_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1060_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_1060_, 0, lean_box(0));
lean_closure_set(v___x_1060_, 1, lean_box(0));
lean_closure_set(v___x_1060_, 2, v___x_1059_);
return v___x_1060_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16(void){
_start:
{
lean_object* v___f_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___f_1061_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11);
v___x_1062_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15);
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v___f_1061_);
return v___x_1063_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1065_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_1065_, 0, lean_box(0));
lean_closure_set(v___x_1065_, 1, lean_box(0));
lean_closure_set(v___x_1065_, 2, v___x_1064_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18(void){
_start:
{
lean_object* v___f_1066_; lean_object* v___f_1067_; lean_object* v___f_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___f_1066_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14);
v___f_1067_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13);
v___f_1068_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12);
v___x_1069_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17);
v___x_1070_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16);
v___x_1071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v___x_1069_);
lean_ctor_set(v___x_1071_, 2, v___f_1068_);
lean_ctor_set(v___x_1071_, 3, v___f_1067_);
lean_ctor_set(v___x_1071_, 4, v___f_1066_);
return v___x_1071_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1073_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_1073_, 0, lean_box(0));
lean_closure_set(v___x_1073_, 1, lean_box(0));
lean_closure_set(v___x_1073_, 2, v___x_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1074_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19);
v___x_1075_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
lean_ctor_set(v___x_1076_, 1, v___x_1074_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1078_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch), 6, 3);
lean_closure_set(v___x_1078_, 0, lean_box(0));
lean_closure_set(v___x_1078_, 1, lean_box(0));
lean_closure_set(v___x_1078_, 2, v___x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg(lean_object* v_inst_1079_, lean_object* v_inst_1080_){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v_toApplicative_1083_; lean_object* v_toPure_1084_; lean_object* v___f_1085_; lean_object* v___f_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___f_1090_; lean_object* v___x_1091_; 
v___x_1081_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1082_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20);
v_toApplicative_1083_ = lean_ctor_get(v___x_1081_, 0);
v_toPure_1084_ = lean_ctor_get(v_toApplicative_1083_, 1);
v___f_1085_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1085_, 0, v_inst_1080_);
lean_inc(v_toPure_1084_);
v___f_1086_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptTOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1086_, 0, v_toPure_1084_);
v___x_1087_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21);
v___x_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___f_1086_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_1088_);
v___f_1090_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1090_, 0, v_inst_1079_);
lean_closure_set(v___f_1090_, 1, v___x_1082_);
lean_closure_set(v___f_1090_, 2, v___x_1089_);
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___f_1085_);
lean_ctor_set(v___x_1091_, 1, v___f_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson(lean_object* v_00_u03b1_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg(v_inst_1093_, v_inst_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg___lam__0(lean_object* v_inst_1096_, lean_object* v___x_1097_, lean_object* v_v_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_fst_1101_; lean_object* v_snd_1102_; 
if (lean_obj_tag(v_v_1098_) == 0)
{
lean_object* v___x_1105_; 
lean_dec_ref(v_inst_1096_);
v___x_1105_ = lean_box(0);
v_fst_1101_ = v___x_1105_;
v_snd_1102_ = v___y_1099_;
goto v___jp_1100_;
}
else
{
lean_object* v_rpcEncode_1106_; lean_object* v_val_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1117_; 
v_rpcEncode_1106_ = lean_ctor_get(v_inst_1096_, 0);
lean_inc_ref(v_rpcEncode_1106_);
lean_dec_ref(v_inst_1096_);
v_val_1107_ = lean_ctor_get(v_v_1098_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_v_1098_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1109_ = v_v_1098_;
v_isShared_1110_ = v_isSharedCheck_1117_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_val_1107_);
lean_dec(v_v_1098_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1117_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v_fst_1112_; lean_object* v_snd_1113_; lean_object* v___x_1115_; 
v___x_1111_ = lean_apply_2(v_rpcEncode_1106_, v_val_1107_, v___y_1099_);
v_fst_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_fst_1112_);
v_snd_1113_ = lean_ctor_get(v___x_1111_, 1);
lean_inc(v_snd_1113_);
lean_dec_ref(v___x_1111_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v_fst_1112_);
v___x_1115_ = v___x_1109_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_fst_1112_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
v_fst_1101_ = v___x_1115_;
v_snd_1102_ = v_snd_1113_;
goto v___jp_1100_;
}
}
}
v___jp_1100_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = l_Option_toJson___redArg(v___x_1097_, v_fst_1101_);
v___x_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
lean_ctor_set(v___x_1104_, 1, v_snd_1102_);
return v___x_1104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg___lam__1(lean_object* v___f_1120_, lean_object* v_inst_1121_, lean_object* v_j_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Option_fromJson_x3f___redArg(v___f_1120_, v_j_1122_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec_ref(v_inst_1121_);
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
else
{
lean_object* v_a_1133_; 
v_a_1133_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_a_1133_);
lean_dec_ref(v___x_1124_);
if (lean_obj_tag(v_a_1133_) == 0)
{
lean_object* v___x_1134_; 
lean_dec_ref(v_inst_1121_);
v___x_1134_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___lam__1___closed__0));
return v___x_1134_;
}
else
{
lean_object* v_rpcDecode_1135_; lean_object* v_val_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1160_; 
v_rpcDecode_1135_ = lean_ctor_get(v_inst_1121_, 1);
lean_inc_ref(v_rpcDecode_1135_);
lean_dec_ref(v_inst_1121_);
v_val_1136_ = lean_ctor_get(v_a_1133_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_a_1133_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1138_ = v_a_1133_;
v_isShared_1139_ = v_isSharedCheck_1160_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_val_1136_);
lean_dec(v_a_1133_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1160_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; 
lean_inc_ref(v___y_1123_);
v___x_1140_ = lean_apply_2(v_rpcDecode_1135_, v_val_1136_, v___y_1123_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_del_object(v___x_1138_);
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1140_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1140_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1159_; 
v_a_1149_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1151_ = v___x_1140_;
v_isShared_1152_ = v_isSharedCheck_1159_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1140_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1159_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v_a_1149_);
v___x_1154_ = v___x_1138_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1156_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1154_);
v___x_1156_ = v___x_1151_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg___lam__1___boxed(lean_object* v___f_1161_, lean_object* v_inst_1162_, lean_object* v_j_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_Server_instRpcEncodableOption___redArg___lam__1(v___f_1161_, v_inst_1162_, v_j_1163_, v___y_1164_);
lean_dec_ref(v___y_1164_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg(lean_object* v_inst_1168_){
_start:
{
lean_object* v___x_1169_; lean_object* v___f_1170_; lean_object* v___f_1171_; lean_object* v___f_1172_; lean_object* v___x_1173_; 
v___x_1169_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__0));
lean_inc_ref(v_inst_1168_);
v___f_1170_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOption___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1170_, 0, v_inst_1168_);
lean_closure_set(v___f_1170_, 1, v___x_1169_);
v___f_1171_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__1));
v___f_1172_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOption___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1172_, 0, v___f_1171_);
lean_closure_set(v___f_1172_, 1, v_inst_1168_);
v___x_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___f_1170_);
lean_ctor_set(v___x_1173_, 1, v___f_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption(lean_object* v_00_u03b1_1174_, lean_object* v_inst_1175_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Lean_Server_instRpcEncodableOption___redArg(v_inst_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__0(lean_object* v_inst_1177_, lean_object* v___x_1178_, lean_object* v___x_1179_, lean_object* v_a_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_rpcEncode_1182_; size_t v_sz_1183_; size_t v___x_1184_; lean_object* v___x_648__overap_1185_; lean_object* v___x_1186_; lean_object* v_fst_1187_; lean_object* v_snd_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1196_; 
v_rpcEncode_1182_ = lean_ctor_get(v_inst_1177_, 0);
lean_inc_ref(v_rpcEncode_1182_);
lean_dec_ref(v_inst_1177_);
v_sz_1183_ = lean_array_size(v_a_1180_);
v___x_1184_ = ((size_t)0ULL);
v___x_648__overap_1185_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1178_, v_rpcEncode_1182_, v_sz_1183_, v___x_1184_, v_a_1180_);
v___x_1186_ = lean_apply_1(v___x_648__overap_1185_, v___y_1181_);
v_fst_1187_ = lean_ctor_get(v___x_1186_, 0);
v_snd_1188_ = lean_ctor_get(v___x_1186_, 1);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1190_ = v___x_1186_;
v_isShared_1191_ = v_isSharedCheck_1196_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_snd_1188_);
lean_inc(v_fst_1187_);
lean_dec(v___x_1186_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1196_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1192_ = l_Array_toJson___redArg(v___x_1179_, v_fst_1187_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1192_);
v___x_1194_ = v___x_1190_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_snd_1188_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__1(lean_object* v___f_1197_, lean_object* v_inst_1198_, lean_object* v___x_1199_, lean_object* v_b_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Array_fromJson_x3f___redArg(v___f_1197_, v_b_1200_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec_ref(v___x_1199_);
lean_dec_ref(v_inst_1198_);
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1202_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
else
{
lean_object* v_a_1211_; lean_object* v_rpcDecode_1212_; size_t v_sz_1213_; size_t v___x_1214_; lean_object* v___x_662__overap_1215_; lean_object* v___x_1216_; 
v_a_1211_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1211_);
lean_dec_ref(v___x_1202_);
v_rpcDecode_1212_ = lean_ctor_get(v_inst_1198_, 1);
lean_inc_ref(v_rpcDecode_1212_);
lean_dec_ref(v_inst_1198_);
v_sz_1213_ = lean_array_size(v_a_1211_);
v___x_1214_ = ((size_t)0ULL);
v___x_662__overap_1215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1199_, v_rpcDecode_1212_, v_sz_1213_, v___x_1214_, v_a_1211_);
lean_inc_ref(v___y_1201_);
v___x_1216_ = lean_apply_1(v___x_662__overap_1215_, v___y_1201_);
return v___x_1216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__1___boxed(lean_object* v___f_1217_, lean_object* v_inst_1218_, lean_object* v___x_1219_, lean_object* v_b_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_Server_instRpcEncodableArray___redArg___lam__1(v___f_1217_, v_inst_1218_, v___x_1219_, v_b_1220_, v___y_1221_);
lean_dec_ref(v___y_1221_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg(lean_object* v_inst_1249_){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___f_1252_; lean_object* v___x_1253_; lean_object* v___f_1254_; lean_object* v___f_1255_; lean_object* v___x_1256_; 
v___x_1250_ = ((lean_object*)(l_Lean_Server_instRpcEncodableArray___redArg___closed__9));
v___x_1251_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__0));
lean_inc_ref(v_inst_1249_);
v___f_1252_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableArray___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1252_, 0, v_inst_1249_);
lean_closure_set(v___f_1252_, 1, v___x_1250_);
lean_closure_set(v___f_1252_, 2, v___x_1251_);
v___x_1253_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20);
v___f_1254_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__1));
v___f_1255_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableArray___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1255_, 0, v___f_1254_);
lean_closure_set(v___f_1255_, 1, v_inst_1249_);
lean_closure_set(v___f_1255_, 2, v___x_1253_);
v___x_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___f_1252_);
lean_ctor_set(v___x_1256_, 1, v___f_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray(lean_object* v_00_u03b1_1257_, lean_object* v_inst_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_Server_instRpcEncodableArray___redArg(v_inst_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg___lam__0(lean_object* v_inst_1260_, lean_object* v_inst_1261_, lean_object* v___x_1262_, lean_object* v_x_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_fst_1265_; lean_object* v_snd_1266_; lean_object* v_rpcEncode_1267_; lean_object* v___x_1268_; lean_object* v_fst_1269_; lean_object* v_snd_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1289_; 
v_fst_1265_ = lean_ctor_get(v_x_1263_, 0);
lean_inc(v_fst_1265_);
v_snd_1266_ = lean_ctor_get(v_x_1263_, 1);
lean_inc(v_snd_1266_);
lean_dec_ref(v_x_1263_);
v_rpcEncode_1267_ = lean_ctor_get(v_inst_1260_, 0);
lean_inc_ref(v_rpcEncode_1267_);
lean_dec_ref(v_inst_1260_);
v___x_1268_ = lean_apply_2(v_rpcEncode_1267_, v_fst_1265_, v___y_1264_);
v_fst_1269_ = lean_ctor_get(v___x_1268_, 0);
v_snd_1270_ = lean_ctor_get(v___x_1268_, 1);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1272_ = v___x_1268_;
v_isShared_1273_ = v_isSharedCheck_1289_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_snd_1270_);
lean_inc(v_fst_1269_);
lean_dec(v___x_1268_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1289_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v_rpcEncode_1274_; lean_object* v___x_1275_; lean_object* v_fst_1276_; lean_object* v_snd_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1288_; 
v_rpcEncode_1274_ = lean_ctor_get(v_inst_1261_, 0);
lean_inc_ref(v_rpcEncode_1274_);
lean_dec_ref(v_inst_1261_);
v___x_1275_ = lean_apply_2(v_rpcEncode_1274_, v_snd_1266_, v_snd_1270_);
v_fst_1276_ = lean_ctor_get(v___x_1275_, 0);
v_snd_1277_ = lean_ctor_get(v___x_1275_, 1);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1279_ = v___x_1275_;
v_isShared_1280_ = v_isSharedCheck_1288_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_snd_1277_);
lean_inc(v_fst_1276_);
lean_dec(v___x_1275_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1288_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 1, v_fst_1276_);
lean_ctor_set(v___x_1279_, 0, v_fst_1269_);
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_fst_1269_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_fst_1276_);
v___x_1282_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
lean_object* v___x_1283_; lean_object* v___x_1285_; 
lean_inc_ref(v___x_1262_);
v___x_1283_ = l_Prod_toJson___redArg(v___x_1262_, v___x_1262_, v___x_1282_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 1, v_snd_1277_);
lean_ctor_set(v___x_1272_, 0, v___x_1283_);
v___x_1285_ = v___x_1272_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_snd_1277_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg___lam__1(lean_object* v___f_1290_, lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_j_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v___x_1295_; 
lean_inc_ref(v___f_1290_);
v___x_1295_ = l_Prod_fromJson_x3f___redArg(v___f_1290_, v___f_1290_, v_j_1293_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v_inst_1292_);
lean_dec_ref(v_inst_1291_);
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1295_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1295_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v_fst_1305_; lean_object* v_snd_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1342_; 
v_a_1304_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_a_1304_);
lean_dec_ref(v___x_1295_);
v_fst_1305_ = lean_ctor_get(v_a_1304_, 0);
v_snd_1306_ = lean_ctor_get(v_a_1304_, 1);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_a_1304_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1308_ = v_a_1304_;
v_isShared_1309_ = v_isSharedCheck_1342_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_snd_1306_);
lean_inc(v_fst_1305_);
lean_dec(v_a_1304_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1342_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v_rpcDecode_1310_; lean_object* v___x_1311_; 
v_rpcDecode_1310_ = lean_ctor_get(v_inst_1291_, 1);
lean_inc_ref(v_rpcDecode_1310_);
lean_dec_ref(v_inst_1291_);
lean_inc_ref(v___y_1294_);
v___x_1311_ = lean_apply_2(v_rpcDecode_1310_, v_fst_1305_, v___y_1294_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_del_object(v___x_1308_);
lean_dec(v_snd_1306_);
lean_dec_ref(v_inst_1292_);
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
lean_object* v_a_1320_; lean_object* v_rpcDecode_1321_; lean_object* v___x_1322_; 
v_a_1320_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1320_);
lean_dec_ref(v___x_1311_);
v_rpcDecode_1321_ = lean_ctor_get(v_inst_1292_, 1);
lean_inc_ref(v_rpcDecode_1321_);
lean_dec_ref(v_inst_1292_);
lean_inc_ref(v___y_1294_);
v___x_1322_ = lean_apply_2(v_rpcDecode_1321_, v_snd_1306_, v___y_1294_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
lean_dec(v_a_1320_);
lean_del_object(v___x_1308_);
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1322_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1322_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1341_; 
v_a_1331_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1333_ = v___x_1322_;
v_isShared_1334_ = v_isSharedCheck_1341_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1322_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1341_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 1, v_a_1331_);
lean_ctor_set(v___x_1308_, 0, v_a_1320_);
v___x_1336_ = v___x_1308_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1320_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1338_; 
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1336_);
v___x_1338_ = v___x_1333_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg___lam__1___boxed(lean_object* v___f_1343_, lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_j_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_Server_instRpcEncodableProd___redArg___lam__1(v___f_1343_, v_inst_1344_, v_inst_1345_, v_j_1346_, v___y_1347_);
lean_dec_ref(v___y_1347_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg(lean_object* v_inst_1349_, lean_object* v_inst_1350_){
_start:
{
lean_object* v___x_1351_; lean_object* v___f_1352_; lean_object* v___f_1353_; lean_object* v___f_1354_; lean_object* v___x_1355_; 
v___x_1351_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__0));
lean_inc_ref(v_inst_1350_);
lean_inc_ref(v_inst_1349_);
v___f_1352_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableProd___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1352_, 0, v_inst_1349_);
lean_closure_set(v___f_1352_, 1, v_inst_1350_);
lean_closure_set(v___f_1352_, 2, v___x_1351_);
v___f_1353_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__1));
v___f_1354_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableProd___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1354_, 0, v___f_1353_);
lean_closure_set(v___f_1354_, 1, v_inst_1349_);
lean_closure_set(v___f_1354_, 2, v_inst_1350_);
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___f_1352_);
lean_ctor_set(v___x_1355_, 1, v___f_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd(lean_object* v_00_u03b1_1356_, lean_object* v_00_u03b2_1357_, lean_object* v_inst_1358_, lean_object* v_inst_1359_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Lean_Server_instRpcEncodableProd___redArg(v_inst_1358_, v_inst_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__0(lean_object* v_inst_1361_, lean_object* v_fn_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_rpcEncode_1364_; lean_object* v___x_1365_; lean_object* v_fst_1366_; lean_object* v_snd_1367_; lean_object* v___x_1368_; 
v_rpcEncode_1364_ = lean_ctor_get(v_inst_1361_, 0);
lean_inc_ref(v_rpcEncode_1364_);
lean_dec_ref(v_inst_1361_);
v___x_1365_ = lean_apply_1(v_fn_1362_, v___y_1363_);
v_fst_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_fst_1366_);
v_snd_1367_ = lean_ctor_get(v___x_1365_, 1);
lean_inc(v_snd_1367_);
lean_dec_ref(v___x_1365_);
v___x_1368_ = lean_apply_2(v_rpcEncode_1364_, v_fst_1366_, v_snd_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1(lean_object* v_inst_1369_, lean_object* v___x_1370_, lean_object* v_j_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_rpcDecode_1373_; lean_object* v___x_1374_; 
v_rpcDecode_1373_ = lean_ctor_get(v_inst_1369_, 1);
lean_inc_ref(v_rpcDecode_1373_);
lean_dec_ref(v_inst_1369_);
lean_inc_ref(v___y_1372_);
v___x_1374_ = lean_apply_2(v_rpcDecode_1373_, v_j_1371_, v___y_1372_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_dec_ref(v___x_1370_);
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1374_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1374_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1391_; 
v_a_1383_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1385_ = v___x_1374_;
v_isShared_1386_ = v_isSharedCheck_1391_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1374_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1391_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1387_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 5);
lean_closure_set(v___x_1387_, 0, lean_box(0));
lean_closure_set(v___x_1387_, 1, lean_box(0));
lean_closure_set(v___x_1387_, 2, v___x_1370_);
lean_closure_set(v___x_1387_, 3, lean_box(0));
lean_closure_set(v___x_1387_, 4, v_a_1383_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1387_);
v___x_1389_ = v___x_1385_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1___boxed(lean_object* v_inst_1392_, lean_object* v___x_1393_, lean_object* v_j_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1(v_inst_1392_, v___x_1393_, v_j_1394_, v___y_1395_);
lean_dec_ref(v___y_1395_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg(lean_object* v_inst_1397_){
_start:
{
lean_object* v___f_1398_; lean_object* v___x_1399_; lean_object* v___f_1400_; lean_object* v___x_1401_; 
lean_inc_ref(v_inst_1397_);
v___f_1398_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1398_, 0, v_inst_1397_);
v___x_1399_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9));
v___f_1400_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1400_, 0, v_inst_1397_);
lean_closure_set(v___f_1400_, 1, v___x_1399_);
v___x_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___f_1398_);
lean_ctor_set(v___x_1401_, 1, v___f_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore(lean_object* v_00_u03b1_1402_, lean_object* v_inst_1403_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg(v_inst_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(lean_object* v_inst_1405_, lean_object* v_r_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v___x_1408_; lean_object* v_fst_1409_; lean_object* v_snd_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1429_; 
v___x_1408_ = l_Lean_Server_rpcStoreRef___redArg(v_inst_1405_, v_r_1406_, v_a_1407_);
v_fst_1409_ = lean_ctor_get(v___x_1408_, 0);
v_snd_1410_ = lean_ctor_get(v___x_1408_, 1);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1412_ = v___x_1408_;
v_isShared_1413_ = v_isSharedCheck_1429_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_snd_1410_);
lean_inc(v_fst_1409_);
lean_dec(v___x_1408_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1429_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___y_1415_; uint8_t v_wireFormat_1426_; 
v_wireFormat_1426_ = lean_ctor_get_uint8(v_snd_1410_, sizeof(void*)*3);
if (v_wireFormat_1426_ == 0)
{
lean_object* v___x_1427_; 
v___x_1427_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0));
v___y_1415_ = v___x_1427_;
goto v___jp_1414_;
}
else
{
lean_object* v___x_1428_; 
v___x_1428_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1));
v___y_1415_ = v___x_1428_;
goto v___jp_1414_;
}
v___jp_1414_:
{
size_t v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1416_ = lean_unbox_usize(v_fst_1409_);
lean_dec(v_fst_1409_);
v___x_1417_ = lean_usize_to_nat(v___x_1416_);
v___x_1418_ = l_Lean_bignumToJson(v___x_1417_);
lean_inc_ref(v___y_1415_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 1, v___x_1418_);
lean_ctor_set(v___x_1412_, 0, v___y_1415_);
v___x_1420_ = v___x_1412_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___y_1415_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1421_ = lean_box(0);
v___x_1422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v___x_1423_ = l_Lean_Json_mkObj(v___x_1422_);
lean_dec_ref(v___x_1422_);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
lean_ctor_set(v___x_1424_, 1, v_snd_1410_);
return v___x_1424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg___boxed(lean_object* v_inst_1430_, lean_object* v_r_1431_, lean_object* v_a_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(v_inst_1430_, v_r_1431_, v_a_1432_);
lean_dec_ref(v_r_1431_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode(lean_object* v_00_u03b1_1434_, lean_object* v_inst_1435_, lean_object* v_r_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(v_inst_1435_, v_r_1436_, v_a_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___boxed(lean_object* v_00_u03b1_1439_, lean_object* v_inst_1440_, lean_object* v_r_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode(v_00_u03b1_1439_, v_inst_1440_, v_r_1441_, v_a_1442_);
lean_dec_ref(v_r_1441_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(lean_object* v_inst_1445_, lean_object* v_j_1446_, lean_object* v_a_1447_){
_start:
{
uint8_t v_wireFormat_1448_; lean_object* v___x_1449_; lean_object* v___y_1451_; 
v_wireFormat_1448_ = lean_ctor_get_uint8(v_a_1447_, sizeof(void*)*3);
v___x_1449_ = ((lean_object*)(l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg___closed__0));
if (v_wireFormat_1448_ == 0)
{
lean_object* v___x_1464_; 
v___x_1464_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0));
v___y_1451_ = v___x_1464_;
goto v___jp_1450_;
}
else
{
lean_object* v___x_1465_; 
v___x_1465_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1));
v___y_1451_ = v___x_1465_;
goto v___jp_1450_;
}
v___jp_1450_:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1446_, v___x_1449_, v___y_1451_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec(v_inst_1445_);
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1452_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1452_);
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
lean_object* v_a_1461_; size_t v___x_1462_; lean_object* v___x_1463_; 
v_a_1461_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_a_1461_);
lean_dec_ref(v___x_1452_);
v___x_1462_ = lean_unbox_usize(v_a_1461_);
lean_dec(v_a_1461_);
v___x_1463_ = l_Lean_Server_rpcGetRef___redArg(v_inst_1445_, v___x_1462_, v_a_1447_);
return v___x_1463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg___boxed(lean_object* v_inst_1466_, lean_object* v_j_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v_inst_1466_, v_j_1467_, v_a_1468_);
lean_dec_ref(v_a_1468_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode(lean_object* v_00_u03b1_1470_, lean_object* v_inst_1471_, lean_object* v_j_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v_inst_1471_, v_j_1472_, v_a_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___boxed(lean_object* v_00_u03b1_1475_, lean_object* v_inst_1476_, lean_object* v_j_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode(v_00_u03b1_1475_, v_inst_1476_, v_j_1477_, v_a_1478_);
lean_dec_ref(v_a_1478_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName___redArg(lean_object* v_inst_1480_){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
lean_inc(v_inst_1480_);
v___x_1481_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___boxed), 4, 2);
lean_closure_set(v___x_1481_, 0, lean_box(0));
lean_closure_set(v___x_1481_, 1, v_inst_1480_);
v___x_1482_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___boxed), 4, 2);
lean_closure_set(v___x_1482_, 0, lean_box(0));
lean_closure_set(v___x_1482_, 1, v_inst_1480_);
v___x_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1481_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName(lean_object* v_00_u03b1_1484_, lean_object* v_inst_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName___redArg(v_inst_1485_);
return v___x_1486_;
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
