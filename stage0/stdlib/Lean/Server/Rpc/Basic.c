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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_of_nat(lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_USize_toUInt64___boxed(lean_object*);
lean_object* l_instDecidableEqUSize___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_bignumToJson(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_ctorIdx___impl___boxed(lean_object*);
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
uint8_t l_Lean_Lsp_instBEqRpcRef_beq(size_t v_x_5_, size_t v_x_6_){
_start:
{
uint8_t v___x_7_; 
v___x_7_ = lean_usize_dec_eq(v_x_5_, v_x_6_);
return v___x_7_;
}
}
LEAN_EXPORT void l_Lean_Lsp_instBEqRpcRef_beq_0interp(lean_interpreter_value* stack)
{
size_t v_x_5_ = stack[0].m_num;
size_t v_x_6_ = stack[1].m_num;
uint8_t v_res_8_;
v_res_8_ = l_Lean_Lsp_instBEqRpcRef_beq(v_x_5_, v_x_6_);
stack->m_num = v_res_8_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqRpcRef_beq___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
size_t v_x_31__boxed_11_; size_t v_x_32__boxed_12_; uint8_t v_res_13_; lean_object* v_r_14_; 
v_x_31__boxed_11_ = lean_unbox_usize(v_x_9_);
lean_dec(v_x_9_);
v_x_32__boxed_12_ = lean_unbox_usize(v_x_10_);
lean_dec(v_x_10_);
v_res_13_ = l_Lean_Lsp_instBEqRpcRef_beq(v_x_31__boxed_11_, v_x_32__boxed_12_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
uint64_t l_Lean_Lsp_instHashableRpcRef_hash(size_t v_x_17_){
_start:
{
uint64_t v___x_18_; uint64_t v___x_19_; uint64_t v___x_20_; 
v___x_18_ = 0ULL;
v___x_19_ = lean_usize_to_uint64(v_x_17_);
v___x_20_ = lean_uint64_mix_hash(v___x_18_, v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT void l_Lean_Lsp_instHashableRpcRef_hash_0interp(lean_interpreter_value* stack)
{
size_t v_x_17_ = stack[0].m_num;
uint64_t v_res_21_;
v_res_21_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_17_);
stack->m_num = v_res_21_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableRpcRef_hash___boxed(lean_object* v_x_22_){
_start:
{
size_t v_x_26__boxed_23_; uint64_t v_res_24_; lean_object* v_r_25_; 
v_x_26__boxed_23_ = lean_unbox_usize(v_x_22_);
lean_dec(v_x_22_);
v_res_24_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_26__boxed_23_);
v_r_25_ = lean_box_uint64(v_res_24_);
return v_r_25_;
}
}
lean_object* l_Lean_Lsp_instToStringRpcRef___lam__0(size_t v_r_28_){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_usize_to_nat(v_r_28_);
v___x_30_ = l_Nat_reprFast(v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT void l_Lean_Lsp_instToStringRpcRef___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_r_28_ = stack[0].m_num;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Lsp_instToStringRpcRef___lam__0(v_r_28_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToStringRpcRef___lam__0___boxed(lean_object* v_r_32_){
_start:
{
size_t v_r_boxed_33_; lean_object* v_res_34_; 
v_r_boxed_33_ = lean_unbox_usize(v_r_32_);
lean_dec(v_r_32_);
v_res_34_ = l_Lean_Lsp_instToStringRpcRef___lam__0(v_r_boxed_33_);
return v_res_34_;
}
}
lean_object* l_Lean_Lsp_RpcWireFormat_ctorIdx___impl(uint8_t v_x_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_box(v_x_37_);
v___x_39_ = lean_obj_tag_nat(v___x_38_);
lean_dec(v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT void l_Lean_Lsp_RpcWireFormat_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_37_ = stack[0].m_num;
lean_object* v_res_40_;
v_res_40_ = l_Lean_Lsp_RpcWireFormat_ctorIdx___impl(v_x_37_);
stack->m_obj
 = v_res_40_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_ctorIdx___impl___boxed(lean_object* v_x_41_){
_start:
{
uint8_t v_x_4__boxed_42_; lean_object* v_res_43_; 
v_x_4__boxed_42_ = lean_unbox(v_x_41_);
v_res_43_ = l_Lean_Lsp_RpcWireFormat_ctorIdx___impl(v_x_4__boxed_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_ctorElim___redArg(lean_object* v_k_44_){
_start:
{
lean_inc(v_k_44_);
return v_k_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_ctorElim___redArg___boxed(lean_object* v_k_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Lsp_RpcWireFormat_ctorElim___redArg(v_k_45_);
lean_dec(v_k_45_);
return v_res_46_;
}
}
lean_object* l_Lean_Lsp_RpcWireFormat_ctorElim(lean_object* v_motive_47_, lean_object* v_ctorIdx_48_, uint8_t v_t_49_, lean_object* v_h_50_, lean_object* v_k_51_){
_start:
{
lean_inc(v_k_51_);
return v_k_51_;
}
}
LEAN_EXPORT void l_Lean_Lsp_RpcWireFormat_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_48_ = stack[1].m_obj;
uint8_t v_t_49_ = stack[2].m_num;
lean_object* v_k_51_ = stack[4].m_obj;
lean_object* v_res_52_;
v_res_52_ = l_Lean_Lsp_RpcWireFormat_ctorElim(lean_box(0), v_ctorIdx_48_, v_t_49_, lean_box(0), v_k_51_);
stack->m_obj
 = v_res_52_;
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
lean_object* l_Lean_Lsp_RpcWireFormat_v0_elim(lean_object* v_motive_63_, uint8_t v_t_64_, lean_object* v_h_65_, lean_object* v_v0_66_){
_start:
{
lean_inc(v_v0_66_);
return v_v0_66_;
}
}
LEAN_EXPORT void l_Lean_Lsp_RpcWireFormat_v0_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_64_ = stack[1].m_num;
lean_object* v_v0_66_ = stack[3].m_obj;
lean_object* v_res_67_;
v_res_67_ = l_Lean_Lsp_RpcWireFormat_v0_elim(lean_box(0), v_t_64_, lean_box(0), v_v0_66_);
stack->m_obj
 = v_res_67_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v0_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_v0_71_){
_start:
{
uint8_t v_t_boxed_72_; lean_object* v_res_73_; 
v_t_boxed_72_ = lean_unbox(v_t_69_);
v_res_73_ = l_Lean_Lsp_RpcWireFormat_v0_elim(v_motive_68_, v_t_boxed_72_, v_h_70_, v_v0_71_);
lean_dec(v_v0_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v1_elim___redArg(lean_object* v_v1_74_){
_start:
{
lean_inc(v_v1_74_);
return v_v1_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v1_elim___redArg___boxed(lean_object* v_v1_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Lsp_RpcWireFormat_v1_elim___redArg(v_v1_75_);
lean_dec(v_v1_75_);
return v_res_76_;
}
}
lean_object* l_Lean_Lsp_RpcWireFormat_v1_elim(lean_object* v_motive_77_, uint8_t v_t_78_, lean_object* v_h_79_, lean_object* v_v1_80_){
_start:
{
lean_inc(v_v1_80_);
return v_v1_80_;
}
}
LEAN_EXPORT void l_Lean_Lsp_RpcWireFormat_v1_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_78_ = stack[1].m_num;
lean_object* v_v1_80_ = stack[3].m_obj;
lean_object* v_res_81_;
v_res_81_ = l_Lean_Lsp_RpcWireFormat_v1_elim(lean_box(0), v_t_78_, lean_box(0), v_v1_80_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v1_elim___boxed(lean_object* v_motive_82_, lean_object* v_t_83_, lean_object* v_h_84_, lean_object* v_v1_85_){
_start:
{
uint8_t v_t_boxed_86_; lean_object* v_res_87_; 
v_t_boxed_86_ = lean_unbox(v_t_83_);
v_res_87_ = l_Lean_Lsp_RpcWireFormat_v1_elim(v_motive_82_, v_t_boxed_86_, v_h_84_, v_v1_85_);
lean_dec(v_v1_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson(lean_object* v_json_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_Json_getTag_x3f(v_json_102_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v___x_104_; 
v___x_104_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__1));
return v___x_104_;
}
else
{
lean_object* v_val_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v_val_105_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_val_105_);
lean_dec_ref_known(v___x_103_, 1);
v___x_106_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__2));
v___x_107_ = lean_string_dec_eq(v_val_105_, v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__3));
v___x_109_ = lean_string_dec_eq(v_val_105_, v___x_108_);
lean_dec(v_val_105_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
v___x_110_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__5));
return v___x_110_;
}
else
{
lean_object* v___x_111_; 
v___x_111_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__6));
return v___x_111_;
}
}
else
{
lean_object* v___x_112_; 
lean_dec(v_val_105_);
v___x_112_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__7));
return v___x_112_;
}
}
}
}
lean_object* l_Lean_Lsp_instToJsonRpcWireFormat_toJson(uint8_t v_x_119_){
_start:
{
if (v_x_119_ == 0)
{
lean_object* v___x_120_; 
v___x_120_ = ((lean_object*)(l_Lean_Lsp_instToJsonRpcWireFormat_toJson___closed__0));
return v___x_120_;
}
else
{
lean_object* v___x_121_; 
v___x_121_ = ((lean_object*)(l_Lean_Lsp_instToJsonRpcWireFormat_toJson___closed__1));
return v___x_121_;
}
}
}
LEAN_EXPORT void l_Lean_Lsp_instToJsonRpcWireFormat_toJson_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_119_ = stack[0].m_num;
lean_object* v_res_122_;
v_res_122_ = l_Lean_Lsp_instToJsonRpcWireFormat_toJson(v_x_119_);
stack->m_obj
 = v_res_122_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcWireFormat_toJson___boxed(lean_object* v_x_123_){
_start:
{
uint8_t v_x_44__boxed_124_; lean_object* v_res_125_; 
v_x_44__boxed_124_ = lean_unbox(v_x_123_);
v_res_125_ = l_Lean_Lsp_instToJsonRpcWireFormat_toJson(v_x_44__boxed_124_);
return v_res_125_;
}
}
lean_object* l_Lean_Lsp_RpcWireFormat_refFieldName(uint8_t v_x_130_){
_start:
{
if (v_x_130_ == 0)
{
lean_object* v___x_131_; 
v___x_131_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0));
return v___x_131_;
}
else
{
lean_object* v___x_132_; 
v___x_132_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1));
return v___x_132_;
}
}
}
LEAN_EXPORT void l_Lean_Lsp_RpcWireFormat_refFieldName_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_130_ = stack[0].m_num;
lean_object* v_res_133_;
v_res_133_ = l_Lean_Lsp_RpcWireFormat_refFieldName(v_x_130_);
stack->m_obj
 = v_res_133_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_refFieldName___boxed(lean_object* v_x_134_){
_start:
{
uint8_t v_x_22__boxed_135_; lean_object* v_res_136_; 
v_x_22__boxed_135_ = lean_unbox(v_x_134_);
v_res_136_ = l_Lean_Lsp_RpcWireFormat_refFieldName(v_x_22__boxed_135_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef_default___redArg(lean_object* v_inst_137_){
_start:
{
size_t v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_usize_once(&l_Lean_Lsp_instInhabitedRpcRef_default___closed__0, &l_Lean_Lsp_instInhabitedRpcRef_default___closed__0_once, _init_l_Lean_Lsp_instInhabitedRpcRef_default___closed__0);
v___x_139_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_139_, 0, v_inst_137_);
lean_ctor_set_usize(v___x_139_, 1, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef_default(lean_object* v_00_u03b1_140_, lean_object* v_inst_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Server_instInhabitedWithRpcRef_default___redArg(v_inst_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef___redArg(lean_object* v_inst_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_Server_instInhabitedWithRpcRef_default___redArg(v_inst_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef(lean_object* v_a_145_, lean_object* v_inst_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Server_instInhabitedWithRpcRef_default___redArg(v_inst_146_);
return v___x_147_;
}
}
lean_object* l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_151_ = ((lean_object*)(l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn___boxed__const__1_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_));
v___x_152_ = lean_st_mk_ref(v___x_151_);
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_154_;
v_res_154_ = l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_();
stack->m_obj
 = v_res_154_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2____boxed(lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_();
return v_res_156_;
}
}
lean_object* l_Lean_Server_WithRpcRef_mk___redArg(lean_object* v_val_157_){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; size_t v___x_161_; size_t v___x_162_; size_t v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; size_t v___x_167_; 
v___x_159_ = l_Lean_Server_freshWithRpcRefId;
v___x_160_ = lean_st_ref_take(v___x_159_);
v___x_161_ = ((size_t)1ULL);
v___x_162_ = lean_unbox_usize(v___x_160_);
v___x_163_ = lean_usize_add(v___x_162_, v___x_161_);
v___x_164_ = lean_box_usize(v___x_163_);
v___x_165_ = lean_st_ref_put(v___x_159_, v___x_164_);
v___x_166_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_166_, 0, v_val_157_);
v___x_167_ = lean_unbox_usize(v___x_160_);
lean_dec(v___x_160_);
lean_ctor_set_usize(v___x_166_, 1, v___x_167_);
return v___x_166_;
}
}
LEAN_EXPORT void l_Lean_Server_WithRpcRef_mk___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_157_ = stack[0].m_obj;
lean_object* v_res_168_;
v_res_168_ = l_Lean_Server_WithRpcRef_mk___redArg(v_val_157_);
stack->m_obj
 = v_res_168_;
}
LEAN_EXPORT lean_object* l_Lean_Server_WithRpcRef_mk___redArg___boxed(lean_object* v_val_169_, lean_object* v_a_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_Server_WithRpcRef_mk___redArg(v_val_169_);
return v_res_171_;
}
}
lean_object* l_Lean_Server_WithRpcRef_mk(lean_object* v_00_u03b1_172_, lean_object* v_val_173_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Server_WithRpcRef_mk___redArg(v_val_173_);
return v___x_175_;
}
}
LEAN_EXPORT void l_Lean_Server_WithRpcRef_mk_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_173_ = stack[1].m_obj;
lean_object* v_res_176_;
v_res_176_ = l_Lean_Server_WithRpcRef_mk(lean_box(0), v_val_173_);
stack->m_obj
 = v_res_176_;
}
LEAN_EXPORT lean_object* l_Lean_Server_WithRpcRef_mk___boxed(lean_object* v_00_u03b1_177_, lean_object* v_val_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Server_WithRpcRef_mk(v_00_u03b1_177_, v_val_178_);
return v_res_180_;
}
}
static lean_object* _init_l_Lean_Server_rpcStoreRef___redArg___closed__1(void){
_start:
{
lean_object* v___x_182_; lean_object* v___f_183_; 
v___x_182_ = lean_alloc_closure((void*)(l_instDecidableEqUSize___boxed), 2, 0);
v___f_183_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_183_, 0, v___x_182_);
return v___f_183_;
}
}
static lean_object* _init_l_Lean_Server_rpcStoreRef___redArg___closed__5(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_187_ = ((lean_object*)(l_Lean_Server_rpcStoreRef___redArg___closed__4));
v___x_188_ = lean_unsigned_to_nat(15u);
v___x_189_ = lean_unsigned_to_nat(132u);
v___x_190_ = ((lean_object*)(l_Lean_Server_rpcStoreRef___redArg___closed__3));
v___x_191_ = ((lean_object*)(l_Lean_Server_rpcStoreRef___redArg___closed__2));
v___x_192_ = l_mkPanicMessageWithDecl(v___x_191_, v___x_190_, v___x_189_, v___x_188_, v___x_187_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_Server_rpcStoreRef___redArg___boxed__const__1(void){
_start:
{
size_t v___x_193_; lean_object* v___x_194_; 
v___x_193_ = l_Lean_Lsp_instInhabitedRpcRef_default;
v___x_194_ = lean_box_usize(v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcStoreRef___redArg(lean_object* v_inst_195_, lean_object* v_obj_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_aliveRefs_198_; lean_object* v_refsById_199_; size_t v_nextRef_200_; uint8_t v_wireFormat_201_; lean_object* v_val_202_; size_t v_id_203_; lean_object* v___f_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___f_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_aliveRefs_198_ = lean_ctor_get(v_a_197_, 0);
v_refsById_199_ = lean_ctor_get(v_a_197_, 1);
v_nextRef_200_ = lean_ctor_get_usize(v_a_197_, 2);
v_wireFormat_201_ = lean_ctor_get_uint8(v_a_197_, sizeof(void*)*3);
v_val_202_ = lean_ctor_get(v_obj_196_, 0);
v_id_203_ = lean_ctor_get_usize(v_obj_196_, 1);
v___f_204_ = ((lean_object*)(l_Lean_Server_rpcStoreRef___redArg___closed__0));
v___x_205_ = ((lean_object*)(l_Lean_Lsp_instBEqRpcRef___closed__0));
v___x_206_ = ((lean_object*)(l_Lean_Lsp_instHashableRpcRef___closed__0));
v___f_207_ = lean_obj_once(&l_Lean_Server_rpcStoreRef___redArg___closed__1, &l_Lean_Server_rpcStoreRef___redArg___closed__1_once, _init_l_Lean_Server_rpcStoreRef___redArg___closed__1);
v___x_208_ = lean_box_usize(v_id_203_);
v___x_209_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_207_, v___f_204_, v_refsById_199_, v___x_208_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_228_; 
lean_inc_ref(v_refsById_199_);
lean_inc_ref(v_aliveRefs_198_);
v_isSharedCheck_228_ = !lean_is_exclusive(v_a_197_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; lean_object* v_unused_230_; 
v_unused_229_ = lean_ctor_get(v_a_197_, 1);
lean_dec(v_unused_229_);
v_unused_230_ = lean_ctor_get(v_a_197_, 0);
lean_dec(v_unused_230_);
v___x_211_ = v_a_197_;
v_isShared_212_ = v_isSharedCheck_228_;
goto v_resetjp_210_;
}
else
{
lean_dec(v_a_197_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_228_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; size_t v___x_221_; size_t v___x_222_; lean_object* v___x_224_; 
lean_inc(v_val_202_);
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v_inst_195_);
lean_ctor_set(v___x_213_, 1, v_val_202_);
v___x_214_ = lean_unsigned_to_nat(1u);
v___x_215_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(v___x_215_, 0, v___x_213_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
lean_ctor_set_usize(v___x_215_, 2, v_id_203_);
v___x_216_ = lean_box_usize(v_nextRef_200_);
v___x_217_ = l_Lean_PersistentHashMap_insert___redArg(v___x_205_, v___x_206_, v_aliveRefs_198_, v___x_216_, v___x_215_);
v___x_218_ = lean_box_usize(v_id_203_);
v___x_219_ = lean_box_usize(v_nextRef_200_);
v___x_220_ = l_Lean_PersistentHashMap_insert___redArg(v___f_207_, v___f_204_, v_refsById_199_, v___x_218_, v___x_219_);
v___x_221_ = ((size_t)1ULL);
v___x_222_ = lean_usize_add(v_nextRef_200_, v___x_221_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 1, v___x_220_);
lean_ctor_set(v___x_211_, 0, v___x_217_);
v___x_224_ = v___x_211_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v___x_220_);
lean_ctor_set_uint8(v_reuseFailAlloc_227_, sizeof(void*)*3, v_wireFormat_201_);
v___x_224_ = v_reuseFailAlloc_227_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_ctor_set_usize(v___x_224_, 2, v___x_222_);
v___x_225_ = lean_box_usize(v_nextRef_200_);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___x_224_);
return v___x_226_;
}
}
}
else
{
lean_object* v_val_231_; lean_object* v___x_232_; 
lean_dec(v_inst_195_);
v_val_231_ = lean_ctor_get(v___x_209_, 0);
lean_inc_n(v_val_231_, 2);
lean_dec_ref_known(v___x_209_, 1);
v___x_232_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_205_, v___x_206_, v_aliveRefs_198_, v_val_231_);
if (lean_obj_tag(v___x_232_) == 1)
{
lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_254_; 
lean_inc_ref(v_refsById_199_);
lean_inc_ref(v_aliveRefs_198_);
v_isSharedCheck_254_ = !lean_is_exclusive(v_a_197_);
if (v_isSharedCheck_254_ == 0)
{
lean_object* v_unused_255_; lean_object* v_unused_256_; 
v_unused_255_ = lean_ctor_get(v_a_197_, 1);
lean_dec(v_unused_255_);
v_unused_256_ = lean_ctor_get(v_a_197_, 0);
lean_dec(v_unused_256_);
v___x_234_ = v_a_197_;
v_isShared_235_ = v_isSharedCheck_254_;
goto v_resetjp_233_;
}
else
{
lean_dec(v_a_197_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_254_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v_val_236_; lean_object* v_obj_237_; size_t v_id_238_; lean_object* v_rc_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_253_; 
v_val_236_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_val_236_);
lean_dec_ref_known(v___x_232_, 1);
v_obj_237_ = lean_ctor_get(v_val_236_, 0);
v_id_238_ = lean_ctor_get_usize(v_val_236_, 2);
v_rc_239_ = lean_ctor_get(v_val_236_, 1);
v_isSharedCheck_253_ = !lean_is_exclusive(v_val_236_);
if (v_isSharedCheck_253_ == 0)
{
v___x_241_ = v_val_236_;
v_isShared_242_ = v_isSharedCheck_253_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_rc_239_);
lean_inc(v_obj_237_);
lean_dec(v_val_236_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_253_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_243_ = lean_unsigned_to_nat(1u);
v___x_244_ = lean_nat_add(v_rc_239_, v___x_243_);
lean_dec(v_rc_239_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v___x_244_);
v___x_246_ = v___x_241_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_obj_237_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v___x_244_);
lean_ctor_set_usize(v_reuseFailAlloc_252_, 2, v_id_238_);
v___x_246_ = v_reuseFailAlloc_252_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; lean_object* v___x_249_; 
lean_inc(v_val_231_);
v___x_247_ = l_Lean_PersistentHashMap_insert___redArg(v___x_205_, v___x_206_, v_aliveRefs_198_, v_val_231_, v___x_246_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v___x_247_);
v___x_249_ = v___x_234_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_refsById_199_);
lean_ctor_set_usize(v_reuseFailAlloc_251_, 2, v_nextRef_200_);
lean_ctor_set_uint8(v_reuseFailAlloc_251_, sizeof(void*)*3, v_wireFormat_201_);
v___x_249_ = v_reuseFailAlloc_251_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; 
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v_val_231_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
return v___x_250_;
}
}
}
}
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec(v___x_232_);
lean_dec(v_val_231_);
v___x_257_ = lean_obj_once(&l_Lean_Server_rpcStoreRef___redArg___closed__5, &l_Lean_Server_rpcStoreRef___redArg___closed__5_once, _init_l_Lean_Server_rpcStoreRef___redArg___closed__5);
v___x_258_ = l_Lean_Server_rpcStoreRef___redArg___boxed__const__1;
v___x_259_ = l_panic___redArg(v___x_258_, v___x_257_);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v_a_197_);
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcStoreRef___redArg___boxed(lean_object* v_inst_261_, lean_object* v_obj_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Server_rpcStoreRef___redArg(v_inst_261_, v_obj_262_, v_a_263_);
lean_dec_ref(v_obj_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcStoreRef(lean_object* v_00_u03b1_265_, lean_object* v_inst_266_, lean_object* v_obj_267_, lean_object* v_a_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_Server_rpcStoreRef___redArg(v_inst_266_, v_obj_267_, v_a_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcStoreRef___boxed(lean_object* v_00_u03b1_270_, lean_object* v_inst_271_, lean_object* v_obj_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Server_rpcStoreRef(v_00_u03b1_270_, v_inst_271_, v_obj_272_, v_a_273_);
lean_dec_ref(v_obj_272_);
return v_res_274_;
}
}
lean_object* l_Lean_Server_rpcGetRef___redArg(lean_object* v_inst_282_, size_t v_r_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_aliveRefs_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_aliveRefs_285_ = lean_ctor_get(v_a_284_, 0);
v___x_286_ = ((lean_object*)(l_Lean_Lsp_instBEqRpcRef___closed__0));
v___x_287_ = ((lean_object*)(l_Lean_Lsp_instHashableRpcRef___closed__0));
v___x_288_ = lean_box_usize(v_r_283_);
v___x_289_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_286_, v___x_287_, v_aliveRefs_285_, v___x_288_);
if (lean_obj_tag(v___x_289_) == 1)
{
lean_object* v_val_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_327_; 
v_val_290_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_327_ == 0)
{
v___x_292_ = v___x_289_;
v_isShared_293_ = v_isSharedCheck_327_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_val_290_);
lean_dec(v___x_289_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_327_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v_obj_294_; size_t v_id_295_; lean_object* v___x_296_; 
v_obj_294_ = lean_ctor_get(v_val_290_, 0);
lean_inc(v_obj_294_);
v_id_295_ = lean_ctor_get_usize(v_val_290_, 2);
lean_dec(v_val_290_);
v___x_296_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_obj_294_, v_inst_282_);
if (lean_obj_tag(v___x_296_) == 1)
{
lean_object* v_val_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_305_; 
lean_dec(v_obj_294_);
lean_del_object(v___x_292_);
lean_dec(v_inst_282_);
v_val_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_305_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_305_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_val_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_305_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_301_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_301_, 0, v_val_297_);
lean_ctor_set_usize(v___x_301_, 1, v_id_295_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_301_);
v___x_303_ = v___x_299_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
lean_dec(v___x_296_);
v___x_306_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__0));
v___x_307_ = lean_usize_to_nat(v_r_283_);
v___x_308_ = l_Nat_reprFast(v___x_307_);
v___x_309_ = lean_string_append(v___x_306_, v___x_308_);
lean_dec_ref(v___x_308_);
v___x_310_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__1));
v___x_311_ = lean_string_append(v___x_309_, v___x_310_);
v___x_312_ = 1;
v___x_313_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_inst_282_, v___x_312_);
v___x_314_ = lean_string_append(v___x_311_, v___x_313_);
lean_dec_ref(v___x_313_);
v___x_315_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__2));
v___x_316_ = lean_string_append(v___x_314_, v___x_315_);
v___x_317_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__3));
v___x_318_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_obj_294_);
lean_dec(v_obj_294_);
v___x_319_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_318_, v___x_312_);
v___x_320_ = lean_string_append(v___x_317_, v___x_319_);
lean_dec_ref(v___x_319_);
v___x_321_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__4));
v___x_322_ = lean_string_append(v___x_320_, v___x_321_);
v___x_323_ = lean_string_append(v___x_316_, v___x_322_);
lean_dec_ref(v___x_322_);
if (v_isShared_293_ == 0)
{
lean_ctor_set_tag(v___x_292_, 0);
lean_ctor_set(v___x_292_, 0, v___x_323_);
v___x_325_ = v___x_292_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec(v___x_289_);
lean_dec(v_inst_282_);
v___x_328_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__5));
v___x_329_ = lean_usize_to_nat(v_r_283_);
v___x_330_ = l_Nat_reprFast(v___x_329_);
v___x_331_ = lean_string_append(v___x_328_, v___x_330_);
lean_dec_ref(v___x_330_);
v___x_332_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__6));
v___x_333_ = lean_string_append(v___x_331_, v___x_332_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
}
LEAN_EXPORT void l_Lean_Server_rpcGetRef___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_282_ = stack[0].m_obj;
size_t v_r_283_ = stack[1].m_num;
lean_object* v_a_284_ = stack[2].m_obj;
lean_object* v_res_335_;
v_res_335_ = l_Lean_Server_rpcGetRef___redArg(v_inst_282_, v_r_283_, v_a_284_);
stack->m_obj
 = v_res_335_;
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcGetRef___redArg___boxed(lean_object* v_inst_336_, lean_object* v_r_337_, lean_object* v_a_338_){
_start:
{
size_t v_r_boxed_339_; lean_object* v_res_340_; 
v_r_boxed_339_ = lean_unbox_usize(v_r_337_);
lean_dec(v_r_337_);
v_res_340_ = l_Lean_Server_rpcGetRef___redArg(v_inst_336_, v_r_boxed_339_, v_a_338_);
lean_dec_ref(v_a_338_);
return v_res_340_;
}
}
lean_object* l_Lean_Server_rpcGetRef(lean_object* v_00_u03b1_341_, lean_object* v_inst_342_, size_t v_r_343_, lean_object* v_a_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_Server_rpcGetRef___redArg(v_inst_342_, v_r_343_, v_a_344_);
return v___x_345_;
}
}
LEAN_EXPORT void l_Lean_Server_rpcGetRef_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_342_ = stack[1].m_obj;
size_t v_r_343_ = stack[2].m_num;
lean_object* v_a_344_ = stack[3].m_obj;
lean_object* v_res_346_;
v_res_346_ = l_Lean_Server_rpcGetRef(lean_box(0), v_inst_342_, v_r_343_, v_a_344_);
stack->m_obj
 = v_res_346_;
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcGetRef___boxed(lean_object* v_00_u03b1_347_, lean_object* v_inst_348_, lean_object* v_r_349_, lean_object* v_a_350_){
_start:
{
size_t v_r_boxed_351_; lean_object* v_res_352_; 
v_r_boxed_351_ = lean_unbox_usize(v_r_349_);
lean_dec(v_r_349_);
v_res_352_ = l_Lean_Server_rpcGetRef(v_00_u03b1_347_, v_inst_348_, v_r_boxed_351_, v_a_350_);
lean_dec_ref(v_a_350_);
return v_res_352_;
}
}
lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11(lean_object* v_xs_353_, size_t v_v_354_, lean_object* v_i_355_){
_start:
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = lean_array_get_size(v_xs_353_);
v___x_357_ = lean_nat_dec_lt(v_i_355_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
lean_dec(v_i_355_);
v___x_358_ = lean_box(0);
return v___x_358_;
}
else
{
lean_object* v___x_359_; size_t v___x_360_; uint8_t v___x_361_; 
v___x_359_ = lean_array_fget_borrowed(v_xs_353_, v_i_355_);
v___x_360_ = lean_unbox_usize(v___x_359_);
v___x_361_ = lean_usize_dec_eq(v___x_360_, v_v_354_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_unsigned_to_nat(1u);
v___x_363_ = lean_nat_add(v_i_355_, v___x_362_);
lean_dec(v_i_355_);
v_i_355_ = v___x_363_;
goto _start;
}
else
{
lean_object* v___x_365_; 
v___x_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_365_, 0, v_i_355_);
return v___x_365_;
}
}
}
}
LEAN_EXPORT void l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_353_ = stack[0].m_obj;
size_t v_v_354_ = stack[1].m_num;
lean_object* v_i_355_ = stack[2].m_obj;
lean_object* v_res_366_;
v_res_366_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11(v_xs_353_, v_v_354_, v_i_355_);
stack->m_obj
 = v_res_366_;
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11___boxed(lean_object* v_xs_367_, lean_object* v_v_368_, lean_object* v_i_369_){
_start:
{
size_t v_v_boxed_370_; lean_object* v_res_371_; 
v_v_boxed_370_ = lean_unbox_usize(v_v_368_);
lean_dec(v_v_368_);
v_res_371_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11(v_xs_367_, v_v_boxed_370_, v_i_369_);
lean_dec_ref(v_xs_367_);
return v_res_371_;
}
}
lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8(lean_object* v_xs_372_, size_t v_v_373_){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11(v_xs_372_, v_v_373_, v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT void l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_372_ = stack[0].m_obj;
size_t v_v_373_ = stack[1].m_num;
lean_object* v_res_376_;
v_res_376_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8(v_xs_372_, v_v_373_);
stack->m_obj
 = v_res_376_;
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8___boxed(lean_object* v_xs_377_, lean_object* v_v_378_){
_start:
{
size_t v_v_boxed_379_; lean_object* v_res_380_; 
v_v_boxed_379_ = lean_unbox_usize(v_v_378_);
lean_dec(v_v_378_);
v_res_380_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8(v_xs_377_, v_v_boxed_379_);
lean_dec_ref(v_xs_377_);
return v_res_380_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(lean_object* v_x_381_, size_t v_x_382_, size_t v_x_383_){
_start:
{
if (lean_obj_tag(v_x_381_) == 0)
{
lean_object* v_es_384_; lean_object* v___x_385_; size_t v___x_386_; size_t v___x_387_; lean_object* v_j_388_; lean_object* v_entry_389_; 
v_es_384_ = lean_ctor_get(v_x_381_, 0);
v___x_385_ = lean_box(2);
v___x_386_ = ((size_t)31ULL);
v___x_387_ = lean_usize_land(v_x_382_, v___x_386_);
v_j_388_ = lean_usize_to_nat(v___x_387_);
v_entry_389_ = lean_array_get(v___x_385_, v_es_384_, v_j_388_);
switch(lean_obj_tag(v_entry_389_))
{
case 0:
{
lean_object* v_key_390_; size_t v___x_391_; uint8_t v___x_392_; 
v_key_390_ = lean_ctor_get(v_entry_389_, 0);
lean_inc(v_key_390_);
lean_dec_ref_known(v_entry_389_, 2);
v___x_391_ = lean_unbox_usize(v_key_390_);
lean_dec(v_key_390_);
v___x_392_ = lean_usize_dec_eq(v_x_383_, v___x_391_);
if (v___x_392_ == 0)
{
lean_dec(v_j_388_);
return v_x_381_;
}
else
{
lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_400_; 
lean_inc_ref(v_es_384_);
v_isSharedCheck_400_ = !lean_is_exclusive(v_x_381_);
if (v_isSharedCheck_400_ == 0)
{
lean_object* v_unused_401_; 
v_unused_401_ = lean_ctor_get(v_x_381_, 0);
lean_dec(v_unused_401_);
v___x_394_ = v_x_381_;
v_isShared_395_ = v_isSharedCheck_400_;
goto v_resetjp_393_;
}
else
{
lean_dec(v_x_381_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_400_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_396_ = lean_array_set(v_es_384_, v_j_388_, v___x_385_);
lean_dec(v_j_388_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_396_);
v___x_398_ = v___x_394_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
case 1:
{
lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_436_; 
lean_inc_ref(v_es_384_);
v_isSharedCheck_436_ = !lean_is_exclusive(v_x_381_);
if (v_isSharedCheck_436_ == 0)
{
lean_object* v_unused_437_; 
v_unused_437_ = lean_ctor_get(v_x_381_, 0);
lean_dec(v_unused_437_);
v___x_403_ = v_x_381_;
v_isShared_404_ = v_isSharedCheck_436_;
goto v_resetjp_402_;
}
else
{
lean_dec(v_x_381_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_436_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v_node_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_435_; 
v_node_405_ = lean_ctor_get(v_entry_389_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v_entry_389_);
if (v_isSharedCheck_435_ == 0)
{
v___x_407_ = v_entry_389_;
v_isShared_408_ = v_isSharedCheck_435_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_node_405_);
lean_dec(v_entry_389_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_435_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
size_t v___x_409_; lean_object* v_entries_410_; size_t v___x_411_; lean_object* v_newNode_412_; lean_object* v___x_413_; 
v___x_409_ = ((size_t)5ULL);
v_entries_410_ = lean_array_set(v_es_384_, v_j_388_, v___x_385_);
v___x_411_ = lean_usize_shift_right(v_x_382_, v___x_409_);
v_newNode_412_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_node_405_, v___x_411_, v_x_383_);
lean_inc_ref(v_newNode_412_);
v___x_413_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_412_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v___x_415_; 
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v_newNode_412_);
v___x_415_ = v___x_407_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_newNode_412_);
v___x_415_ = v_reuseFailAlloc_420_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_416_ = lean_array_set(v_entries_410_, v_j_388_, v___x_415_);
lean_dec(v_j_388_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_416_);
v___x_418_ = v___x_403_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
else
{
lean_object* v_val_421_; lean_object* v_fst_422_; lean_object* v_snd_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_434_; 
lean_dec_ref(v_newNode_412_);
lean_del_object(v___x_407_);
v_val_421_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_val_421_);
lean_dec_ref_known(v___x_413_, 1);
v_fst_422_ = lean_ctor_get(v_val_421_, 0);
v_snd_423_ = lean_ctor_get(v_val_421_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_val_421_);
if (v_isSharedCheck_434_ == 0)
{
v___x_425_ = v_val_421_;
v_isShared_426_ = v_isSharedCheck_434_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_snd_423_);
lean_inc(v_fst_422_);
lean_dec(v_val_421_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_434_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_fst_422_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_snd_423_);
v___x_428_ = v_reuseFailAlloc_433_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_429_ = lean_array_set(v_entries_410_, v_j_388_, v___x_428_);
lean_dec(v_j_388_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_429_);
v___x_431_ = v___x_403_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_388_);
return v_x_381_;
}
}
}
else
{
lean_object* v_ks_438_; lean_object* v_vs_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_453_; 
v_ks_438_ = lean_ctor_get(v_x_381_, 0);
v_vs_439_ = lean_ctor_get(v_x_381_, 1);
v_isSharedCheck_453_ = !lean_is_exclusive(v_x_381_);
if (v_isSharedCheck_453_ == 0)
{
v___x_441_ = v_x_381_;
v_isShared_442_ = v_isSharedCheck_453_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_vs_439_);
lean_inc(v_ks_438_);
lean_dec(v_x_381_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_453_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; 
v___x_443_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8(v_ks_438_, v_x_383_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v___x_445_; 
if (v_isShared_442_ == 0)
{
v___x_445_ = v___x_441_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_ks_438_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_vs_439_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
else
{
lean_object* v_val_447_; lean_object* v_keys_x27_448_; lean_object* v_vals_x27_449_; lean_object* v___x_451_; 
v_val_447_ = lean_ctor_get(v___x_443_, 0);
lean_inc_n(v_val_447_, 2);
lean_dec_ref_known(v___x_443_, 1);
v_keys_x27_448_ = l_Array_eraseIdx___redArg(v_ks_438_, v_val_447_);
v_vals_x27_449_ = l_Array_eraseIdx___redArg(v_vs_439_, v_val_447_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 1, v_vals_x27_449_);
lean_ctor_set(v___x_441_, 0, v_keys_x27_448_);
v___x_451_ = v___x_441_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_keys_x27_448_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_vals_x27_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_381_ = stack[0].m_obj;
size_t v_x_382_ = stack[1].m_num;
size_t v_x_383_ = stack[2].m_num;
lean_object* v_res_454_;
v_res_454_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_x_381_, v_x_382_, v_x_383_);
stack->m_obj
 = v_res_454_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___boxed(lean_object* v_x_455_, lean_object* v_x_456_, lean_object* v_x_457_){
_start:
{
size_t v_x_1675__boxed_458_; size_t v_x_1676__boxed_459_; lean_object* v_res_460_; 
v_x_1675__boxed_458_ = lean_unbox_usize(v_x_456_);
lean_dec(v_x_456_);
v_x_1676__boxed_459_ = lean_unbox_usize(v_x_457_);
lean_dec(v_x_457_);
v_res_460_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_x_455_, v_x_1675__boxed_458_, v_x_1676__boxed_459_);
return v_res_460_;
}
}
lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(lean_object* v_x_461_, size_t v_x_462_){
_start:
{
uint64_t v___x_463_; size_t v_h_464_; lean_object* v___x_465_; 
v___x_463_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_462_);
v_h_464_ = lean_uint64_to_usize(v___x_463_);
v___x_465_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_x_461_, v_h_464_, v_x_462_);
return v___x_465_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_461_ = stack[0].m_obj;
size_t v_x_462_ = stack[1].m_num;
lean_object* v_res_466_;
v_res_466_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(v_x_461_, v_x_462_);
stack->m_obj
 = v_res_466_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg___boxed(lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
size_t v_x_1883__boxed_469_; lean_object* v_res_470_; 
v_x_1883__boxed_469_ = lean_unbox_usize(v_x_468_);
lean_dec(v_x_468_);
v_res_470_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(v_x_467_, v_x_1883__boxed_469_);
return v_res_470_;
}
}
lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_471_, lean_object* v_vals_472_, lean_object* v_i_473_, size_t v_k_474_){
_start:
{
lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_475_ = lean_array_get_size(v_keys_471_);
v___x_476_ = lean_nat_dec_lt(v_i_473_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; 
lean_dec(v_i_473_);
v___x_477_ = lean_box(0);
return v___x_477_;
}
else
{
lean_object* v_k_x27_478_; size_t v___x_479_; uint8_t v___x_480_; 
v_k_x27_478_ = lean_array_fget_borrowed(v_keys_471_, v_i_473_);
v___x_479_ = lean_unbox_usize(v_k_x27_478_);
v___x_480_ = lean_usize_dec_eq(v_k_474_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_unsigned_to_nat(1u);
v___x_482_ = lean_nat_add(v_i_473_, v___x_481_);
lean_dec(v_i_473_);
v_i_473_ = v___x_482_;
goto _start;
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_array_fget_borrowed(v_vals_472_, v_i_473_);
lean_dec(v_i_473_);
lean_inc(v___x_484_);
v___x_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
return v___x_485_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_471_ = stack[0].m_obj;
lean_object* v_vals_472_ = stack[1].m_obj;
lean_object* v_i_473_ = stack[2].m_obj;
size_t v_k_474_ = stack[3].m_num;
lean_object* v_res_486_;
v_res_486_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(v_keys_471_, v_vals_472_, v_i_473_, v_k_474_);
stack->m_obj
 = v_res_486_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_487_, lean_object* v_vals_488_, lean_object* v_i_489_, lean_object* v_k_490_){
_start:
{
size_t v_k_boxed_491_; lean_object* v_res_492_; 
v_k_boxed_491_ = lean_unbox_usize(v_k_490_);
lean_dec(v_k_490_);
v_res_492_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(v_keys_487_, v_vals_488_, v_i_489_, v_k_boxed_491_);
lean_dec_ref(v_vals_488_);
lean_dec_ref(v_keys_487_);
return v_res_492_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(lean_object* v_x_493_, size_t v_x_494_, size_t v_x_495_){
_start:
{
if (lean_obj_tag(v_x_493_) == 0)
{
lean_object* v_es_496_; lean_object* v___x_497_; size_t v___x_498_; size_t v___x_499_; lean_object* v_j_500_; lean_object* v___x_501_; 
v_es_496_ = lean_ctor_get(v_x_493_, 0);
v___x_497_ = lean_box(2);
v___x_498_ = ((size_t)31ULL);
v___x_499_ = lean_usize_land(v_x_494_, v___x_498_);
v_j_500_ = lean_usize_to_nat(v___x_499_);
v___x_501_ = lean_array_get_borrowed(v___x_497_, v_es_496_, v_j_500_);
lean_dec(v_j_500_);
switch(lean_obj_tag(v___x_501_))
{
case 0:
{
lean_object* v_key_502_; lean_object* v_val_503_; size_t v___x_504_; uint8_t v___x_505_; 
v_key_502_ = lean_ctor_get(v___x_501_, 0);
v_val_503_ = lean_ctor_get(v___x_501_, 1);
v___x_504_ = lean_unbox_usize(v_key_502_);
v___x_505_ = lean_usize_dec_eq(v_x_495_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; 
v___x_506_ = lean_box(0);
return v___x_506_;
}
else
{
lean_object* v___x_507_; 
lean_inc(v_val_503_);
v___x_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_507_, 0, v_val_503_);
return v___x_507_;
}
}
case 1:
{
lean_object* v_node_508_; size_t v___x_509_; size_t v___x_510_; 
v_node_508_ = lean_ctor_get(v___x_501_, 0);
v___x_509_ = ((size_t)5ULL);
v___x_510_ = lean_usize_shift_right(v_x_494_, v___x_509_);
v_x_493_ = v_node_508_;
v_x_494_ = v___x_510_;
goto _start;
}
default: 
{
lean_object* v___x_512_; 
v___x_512_ = lean_box(0);
return v___x_512_;
}
}
}
else
{
lean_object* v_ks_513_; lean_object* v_vs_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v_ks_513_ = lean_ctor_get(v_x_493_, 0);
v_vs_514_ = lean_ctor_get(v_x_493_, 1);
v___x_515_ = lean_unsigned_to_nat(0u);
v___x_516_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(v_ks_513_, v_vs_514_, v___x_515_, v_x_495_);
return v___x_516_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_493_ = stack[0].m_obj;
size_t v_x_494_ = stack[1].m_num;
size_t v_x_495_ = stack[2].m_num;
lean_object* v_res_517_;
v_res_517_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_493_, v_x_494_, v_x_495_);
stack->m_obj
 = v_res_517_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg___boxed(lean_object* v_x_518_, lean_object* v_x_519_, lean_object* v_x_520_){
_start:
{
size_t v_x_1929__boxed_521_; size_t v_x_1930__boxed_522_; lean_object* v_res_523_; 
v_x_1929__boxed_521_ = lean_unbox_usize(v_x_519_);
lean_dec(v_x_519_);
v_x_1930__boxed_522_ = lean_unbox_usize(v_x_520_);
lean_dec(v_x_520_);
v_res_523_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_518_, v_x_1929__boxed_521_, v_x_1930__boxed_522_);
lean_dec_ref(v_x_518_);
return v_res_523_;
}
}
lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(lean_object* v_x_524_, size_t v_x_525_){
_start:
{
uint64_t v___x_526_; size_t v___x_527_; lean_object* v___x_528_; 
v___x_526_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_525_);
v___x_527_ = lean_uint64_to_usize(v___x_526_);
v___x_528_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_524_, v___x_527_, v_x_525_);
return v___x_528_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_524_ = stack[0].m_obj;
size_t v_x_525_ = stack[1].m_num;
lean_object* v_res_529_;
v_res_529_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(v_x_524_, v_x_525_);
stack->m_obj
 = v_res_529_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg___boxed(lean_object* v_x_530_, lean_object* v_x_531_){
_start:
{
size_t v_x_2004__boxed_532_; lean_object* v_res_533_; 
v_x_2004__boxed_532_ = lean_unbox_usize(v_x_531_);
lean_dec(v_x_531_);
v_res_533_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(v_x_530_, v_x_2004__boxed_532_);
lean_dec_ref(v_x_530_);
return v_res_533_;
}
}
lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(lean_object* v_xs_534_, size_t v_v_535_, lean_object* v_i_536_){
_start:
{
lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_537_ = lean_array_get_size(v_xs_534_);
v___x_538_ = lean_nat_dec_lt(v_i_536_, v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; 
lean_dec(v_i_536_);
v___x_539_ = lean_box(0);
return v___x_539_;
}
else
{
lean_object* v___x_540_; size_t v___x_541_; uint8_t v___x_542_; 
v___x_540_ = lean_array_fget_borrowed(v_xs_534_, v_i_536_);
v___x_541_ = lean_unbox_usize(v___x_540_);
v___x_542_ = lean_usize_dec_eq(v___x_541_, v_v_535_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_unsigned_to_nat(1u);
v___x_544_ = lean_nat_add(v_i_536_, v___x_543_);
lean_dec(v_i_536_);
v_i_536_ = v___x_544_;
goto _start;
}
else
{
lean_object* v___x_546_; 
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v_i_536_);
return v___x_546_;
}
}
}
}
LEAN_EXPORT void l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_534_ = stack[0].m_obj;
size_t v_v_535_ = stack[1].m_num;
lean_object* v_i_536_ = stack[2].m_obj;
lean_object* v_res_547_;
v_res_547_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(v_xs_534_, v_v_535_, v_i_536_);
stack->m_obj
 = v_res_547_;
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14___boxed(lean_object* v_xs_548_, lean_object* v_v_549_, lean_object* v_i_550_){
_start:
{
size_t v_v_boxed_551_; lean_object* v_res_552_; 
v_v_boxed_551_ = lean_unbox_usize(v_v_549_);
lean_dec(v_v_549_);
v_res_552_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(v_xs_548_, v_v_boxed_551_, v_i_550_);
lean_dec_ref(v_xs_548_);
return v_res_552_;
}
}
lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(lean_object* v_xs_553_, size_t v_v_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(v_xs_553_, v_v_554_, v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT void l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_553_ = stack[0].m_obj;
size_t v_v_554_ = stack[1].m_num;
lean_object* v_res_557_;
v_res_557_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(v_xs_553_, v_v_554_);
stack->m_obj
 = v_res_557_;
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11___boxed(lean_object* v_xs_558_, lean_object* v_v_559_){
_start:
{
size_t v_v_boxed_560_; lean_object* v_res_561_; 
v_v_boxed_560_ = lean_unbox_usize(v_v_559_);
lean_dec(v_v_559_);
v_res_561_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(v_xs_558_, v_v_boxed_560_);
lean_dec_ref(v_xs_558_);
return v_res_561_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(lean_object* v_x_562_, size_t v_x_563_, size_t v_x_564_){
_start:
{
if (lean_obj_tag(v_x_562_) == 0)
{
lean_object* v_es_565_; lean_object* v___x_566_; size_t v___x_567_; size_t v___x_568_; lean_object* v_j_569_; lean_object* v_entry_570_; 
v_es_565_ = lean_ctor_get(v_x_562_, 0);
v___x_566_ = lean_box(2);
v___x_567_ = ((size_t)31ULL);
v___x_568_ = lean_usize_land(v_x_563_, v___x_567_);
v_j_569_ = lean_usize_to_nat(v___x_568_);
v_entry_570_ = lean_array_get(v___x_566_, v_es_565_, v_j_569_);
switch(lean_obj_tag(v_entry_570_))
{
case 0:
{
lean_object* v_key_571_; size_t v___x_572_; uint8_t v___x_573_; 
v_key_571_ = lean_ctor_get(v_entry_570_, 0);
lean_inc(v_key_571_);
lean_dec_ref_known(v_entry_570_, 2);
v___x_572_ = lean_unbox_usize(v_key_571_);
lean_dec(v_key_571_);
v___x_573_ = lean_usize_dec_eq(v_x_564_, v___x_572_);
if (v___x_573_ == 0)
{
lean_dec(v_j_569_);
return v_x_562_;
}
else
{
lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_581_; 
lean_inc_ref(v_es_565_);
v_isSharedCheck_581_ = !lean_is_exclusive(v_x_562_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; 
v_unused_582_ = lean_ctor_get(v_x_562_, 0);
lean_dec(v_unused_582_);
v___x_575_ = v_x_562_;
v_isShared_576_ = v_isSharedCheck_581_;
goto v_resetjp_574_;
}
else
{
lean_dec(v_x_562_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_581_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; lean_object* v___x_579_; 
v___x_577_ = lean_array_set(v_es_565_, v_j_569_, v___x_566_);
lean_dec(v_j_569_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_577_);
v___x_579_ = v___x_575_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
case 1:
{
lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_617_; 
lean_inc_ref(v_es_565_);
v_isSharedCheck_617_ = !lean_is_exclusive(v_x_562_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; 
v_unused_618_ = lean_ctor_get(v_x_562_, 0);
lean_dec(v_unused_618_);
v___x_584_ = v_x_562_;
v_isShared_585_ = v_isSharedCheck_617_;
goto v_resetjp_583_;
}
else
{
lean_dec(v_x_562_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_617_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v_node_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_616_; 
v_node_586_ = lean_ctor_get(v_entry_570_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v_entry_570_);
if (v_isSharedCheck_616_ == 0)
{
v___x_588_ = v_entry_570_;
v_isShared_589_ = v_isSharedCheck_616_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_node_586_);
lean_dec(v_entry_570_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_616_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
size_t v___x_590_; lean_object* v_entries_591_; size_t v___x_592_; lean_object* v_newNode_593_; lean_object* v___x_594_; 
v___x_590_ = ((size_t)5ULL);
v_entries_591_ = lean_array_set(v_es_565_, v_j_569_, v___x_566_);
v___x_592_ = lean_usize_shift_right(v_x_563_, v___x_590_);
v_newNode_593_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_node_586_, v___x_592_, v_x_564_);
lean_inc_ref(v_newNode_593_);
v___x_594_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_593_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v___x_596_; 
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v_newNode_593_);
v___x_596_ = v___x_588_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_newNode_593_);
v___x_596_ = v_reuseFailAlloc_601_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_597_ = lean_array_set(v_entries_591_, v_j_569_, v___x_596_);
lean_dec(v_j_569_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_597_);
v___x_599_ = v___x_584_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
else
{
lean_object* v_val_602_; lean_object* v_fst_603_; lean_object* v_snd_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref(v_newNode_593_);
lean_del_object(v___x_588_);
v_val_602_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_val_602_);
lean_dec_ref_known(v___x_594_, 1);
v_fst_603_ = lean_ctor_get(v_val_602_, 0);
v_snd_604_ = lean_ctor_get(v_val_602_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v_val_602_);
if (v_isSharedCheck_615_ == 0)
{
v___x_606_ = v_val_602_;
v_isShared_607_ = v_isSharedCheck_615_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_snd_604_);
lean_inc(v_fst_603_);
lean_dec(v_val_602_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_615_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_fst_603_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_snd_604_);
v___x_609_ = v_reuseFailAlloc_614_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_610_ = lean_array_set(v_entries_591_, v_j_569_, v___x_609_);
lean_dec(v_j_569_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_610_);
v___x_612_ = v___x_584_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_569_);
return v_x_562_;
}
}
}
else
{
lean_object* v_ks_619_; lean_object* v_vs_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_634_; 
v_ks_619_ = lean_ctor_get(v_x_562_, 0);
v_vs_620_ = lean_ctor_get(v_x_562_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v_x_562_);
if (v_isSharedCheck_634_ == 0)
{
v___x_622_ = v_x_562_;
v_isShared_623_ = v_isSharedCheck_634_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_vs_620_);
lean_inc(v_ks_619_);
lean_dec(v_x_562_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_634_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; 
v___x_624_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(v_ks_619_, v_x_564_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v___x_626_; 
if (v_isShared_623_ == 0)
{
v___x_626_ = v___x_622_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_ks_619_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_vs_620_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
else
{
lean_object* v_val_628_; lean_object* v_keys_x27_629_; lean_object* v_vals_x27_630_; lean_object* v___x_632_; 
v_val_628_ = lean_ctor_get(v___x_624_, 0);
lean_inc_n(v_val_628_, 2);
lean_dec_ref_known(v___x_624_, 1);
v_keys_x27_629_ = l_Array_eraseIdx___redArg(v_ks_619_, v_val_628_);
v_vals_x27_630_ = l_Array_eraseIdx___redArg(v_vs_620_, v_val_628_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v_vals_x27_630_);
lean_ctor_set(v___x_622_, 0, v_keys_x27_629_);
v___x_632_ = v___x_622_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_keys_x27_629_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_vals_x27_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_562_ = stack[0].m_obj;
size_t v_x_563_ = stack[1].m_num;
size_t v_x_564_ = stack[2].m_num;
lean_object* v_res_635_;
v_res_635_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_562_, v_x_563_, v_x_564_);
stack->m_obj
 = v_res_635_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg___boxed(lean_object* v_x_636_, lean_object* v_x_637_, lean_object* v_x_638_){
_start:
{
size_t v_x_2059__boxed_639_; size_t v_x_2060__boxed_640_; lean_object* v_res_641_; 
v_x_2059__boxed_639_ = lean_unbox_usize(v_x_637_);
lean_dec(v_x_637_);
v_x_2060__boxed_640_ = lean_unbox_usize(v_x_638_);
lean_dec(v_x_638_);
v_res_641_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_636_, v_x_2059__boxed_639_, v_x_2060__boxed_640_);
return v_res_641_;
}
}
lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(lean_object* v_x_642_, size_t v_x_643_){
_start:
{
uint64_t v___x_644_; size_t v_h_645_; lean_object* v___x_646_; 
v___x_644_ = lean_usize_to_uint64(v_x_643_);
v_h_645_ = lean_uint64_to_usize(v___x_644_);
v___x_646_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_642_, v_h_645_, v_x_643_);
return v___x_646_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_642_ = stack[0].m_obj;
size_t v_x_643_ = stack[1].m_num;
lean_object* v_res_647_;
v_res_647_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(v_x_642_, v_x_643_);
stack->m_obj
 = v_res_647_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg___boxed(lean_object* v_x_648_, lean_object* v_x_649_){
_start:
{
size_t v_x_2267__boxed_650_; lean_object* v_res_651_; 
v_x_2267__boxed_650_ = lean_unbox_usize(v_x_649_);
lean_dec(v_x_649_);
v_res_651_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(v_x_648_, v_x_2267__boxed_650_);
return v_res_651_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_x_652_, lean_object* v_x_653_, size_t v_x_654_, lean_object* v_x_655_){
_start:
{
lean_object* v_ks_656_; lean_object* v_vs_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_684_; 
v_ks_656_ = lean_ctor_get(v_x_652_, 0);
v_vs_657_ = lean_ctor_get(v_x_652_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v_x_652_);
if (v_isSharedCheck_684_ == 0)
{
v___x_659_ = v_x_652_;
v_isShared_660_ = v_isSharedCheck_684_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_vs_657_);
lean_inc(v_ks_656_);
lean_dec(v_x_652_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_684_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_661_ = lean_array_get_size(v_ks_656_);
v___x_662_ = lean_nat_dec_lt(v_x_653_, v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
lean_dec(v_x_653_);
v___x_663_ = lean_box_usize(v_x_654_);
v___x_664_ = lean_array_push(v_ks_656_, v___x_663_);
v___x_665_ = lean_array_push(v_vs_657_, v_x_655_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___x_665_);
lean_ctor_set(v___x_659_, 0, v___x_664_);
v___x_667_ = v___x_659_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_664_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
else
{
lean_object* v_k_x27_669_; size_t v___x_670_; uint8_t v___x_671_; 
v_k_x27_669_ = lean_array_fget_borrowed(v_ks_656_, v_x_653_);
v___x_670_ = lean_unbox_usize(v_k_x27_669_);
v___x_671_ = lean_usize_dec_eq(v_x_654_, v___x_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_673_; 
if (v_isShared_660_ == 0)
{
v___x_673_ = v___x_659_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_ks_656_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_vs_657_);
v___x_673_ = v_reuseFailAlloc_677_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_unsigned_to_nat(1u);
v___x_675_ = lean_nat_add(v_x_653_, v___x_674_);
lean_dec(v_x_653_);
v_x_652_ = v___x_673_;
v_x_653_ = v___x_675_;
goto _start;
}
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_678_ = lean_box_usize(v_x_654_);
v___x_679_ = lean_array_fset(v_ks_656_, v_x_653_, v___x_678_);
v___x_680_ = lean_array_fset(v_vs_657_, v_x_653_, v_x_655_);
lean_dec(v_x_653_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___x_680_);
lean_ctor_set(v___x_659_, 0, v___x_679_);
v___x_682_ = v___x_659_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v___x_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_652_ = stack[0].m_obj;
lean_object* v_x_653_ = stack[1].m_obj;
size_t v_x_654_ = stack[2].m_num;
lean_object* v_x_655_ = stack[3].m_obj;
lean_object* v_res_685_;
v_res_685_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_x_652_, v_x_653_, v_x_654_, v_x_655_);
stack->m_obj
 = v_res_685_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_x_686_, lean_object* v_x_687_, lean_object* v_x_688_, lean_object* v_x_689_){
_start:
{
size_t v_x_2284__boxed_690_; lean_object* v_res_691_; 
v_x_2284__boxed_690_ = lean_unbox_usize(v_x_688_);
lean_dec(v_x_688_);
v_res_691_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_x_686_, v_x_687_, v_x_2284__boxed_690_, v_x_689_);
return v_res_691_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(lean_object* v_n_692_, size_t v_k_693_, lean_object* v_v_694_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_unsigned_to_nat(0u);
v___x_696_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_n_692_, v___x_695_, v_k_693_, v_v_694_);
return v___x_696_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_692_ = stack[0].m_obj;
size_t v_k_693_ = stack[1].m_num;
lean_object* v_v_694_ = stack[2].m_obj;
lean_object* v_res_697_;
v_res_697_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v_n_692_, v_k_693_, v_v_694_);
stack->m_obj
 = v_res_697_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_n_698_, lean_object* v_k_699_, lean_object* v_v_700_){
_start:
{
size_t v_k_boxed_701_; lean_object* v_res_702_; 
v_k_boxed_701_ = lean_unbox_usize(v_k_699_);
lean_dec(v_k_699_);
v_res_702_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v_n_698_, v_k_boxed_701_, v_v_700_);
return v_res_702_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_703_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(lean_object* v_x_704_, size_t v_x_705_, size_t v_x_706_, size_t v_x_707_, lean_object* v_x_708_){
_start:
{
if (lean_obj_tag(v_x_704_) == 0)
{
lean_object* v_es_709_; size_t v___x_710_; size_t v___x_711_; lean_object* v_j_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v_es_709_ = lean_ctor_get(v_x_704_, 0);
v___x_710_ = ((size_t)31ULL);
v___x_711_ = lean_usize_land(v_x_705_, v___x_710_);
v_j_712_ = lean_usize_to_nat(v___x_711_);
v___x_713_ = lean_array_get_size(v_es_709_);
v___x_714_ = lean_nat_dec_lt(v_j_712_, v___x_713_);
if (v___x_714_ == 0)
{
lean_dec(v_j_712_);
lean_dec(v_x_708_);
return v_x_704_;
}
else
{
lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_757_; 
lean_inc_ref(v_es_709_);
v_isSharedCheck_757_ = !lean_is_exclusive(v_x_704_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; 
v_unused_758_ = lean_ctor_get(v_x_704_, 0);
lean_dec(v_unused_758_);
v___x_716_ = v_x_704_;
v_isShared_717_ = v_isSharedCheck_757_;
goto v_resetjp_715_;
}
else
{
lean_dec(v_x_704_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_757_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v_v_718_; lean_object* v___x_719_; lean_object* v_xs_x27_720_; lean_object* v___y_722_; 
v_v_718_ = lean_array_fget(v_es_709_, v_j_712_);
v___x_719_ = lean_box(0);
v_xs_x27_720_ = lean_array_fset(v_es_709_, v_j_712_, v___x_719_);
switch(lean_obj_tag(v_v_718_))
{
case 0:
{
lean_object* v_key_727_; lean_object* v_val_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_741_; 
v_key_727_ = lean_ctor_get(v_v_718_, 0);
v_val_728_ = lean_ctor_get(v_v_718_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v_v_718_);
if (v_isSharedCheck_741_ == 0)
{
v___x_730_ = v_v_718_;
v_isShared_731_ = v_isSharedCheck_741_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_val_728_);
lean_inc(v_key_727_);
lean_dec(v_v_718_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_741_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
size_t v___x_732_; uint8_t v___x_733_; 
v___x_732_ = lean_unbox_usize(v_key_727_);
v___x_733_ = lean_usize_dec_eq(v_x_707_, v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
lean_del_object(v___x_730_);
v___x_734_ = lean_box_usize(v_x_707_);
v___x_735_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_727_, v_val_728_, v___x_734_, v_x_708_);
v___x_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
v___y_722_ = v___x_736_;
goto v___jp_721_;
}
else
{
lean_object* v___x_737_; lean_object* v___x_739_; 
lean_dec(v_val_728_);
lean_dec(v_key_727_);
v___x_737_ = lean_box_usize(v_x_707_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v_x_708_);
lean_ctor_set(v___x_730_, 0, v___x_737_);
v___x_739_ = v___x_730_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_x_708_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
v___y_722_ = v___x_739_;
goto v___jp_721_;
}
}
}
}
case 1:
{
lean_object* v_node_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_754_; 
v_node_742_ = lean_ctor_get(v_v_718_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v_v_718_);
if (v_isSharedCheck_754_ == 0)
{
v___x_744_ = v_v_718_;
v_isShared_745_ = v_isSharedCheck_754_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_node_742_);
lean_dec(v_v_718_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_754_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
size_t v___x_746_; size_t v___x_747_; size_t v___x_748_; size_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_746_ = ((size_t)5ULL);
v___x_747_ = lean_usize_shift_right(v_x_705_, v___x_746_);
v___x_748_ = ((size_t)1ULL);
v___x_749_ = lean_usize_add(v_x_706_, v___x_748_);
v___x_750_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_node_742_, v___x_747_, v___x_749_, v_x_707_, v_x_708_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_750_);
v___x_752_ = v___x_744_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
v___y_722_ = v___x_752_;
goto v___jp_721_;
}
}
}
default: 
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_box_usize(v_x_707_);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v_x_708_);
v___y_722_ = v___x_756_;
goto v___jp_721_;
}
}
v___jp_721_:
{
lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_723_ = lean_array_fset(v_xs_x27_720_, v_j_712_, v___y_722_);
lean_dec(v_j_712_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_723_);
v___x_725_ = v___x_716_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
else
{
lean_object* v_ks_759_; lean_object* v_vs_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_778_; 
v_ks_759_ = lean_ctor_get(v_x_704_, 0);
v_vs_760_ = lean_ctor_get(v_x_704_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_x_704_);
if (v_isSharedCheck_778_ == 0)
{
v___x_762_ = v_x_704_;
v_isShared_763_ = v_isSharedCheck_778_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_vs_760_);
lean_inc(v_ks_759_);
lean_dec(v_x_704_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_778_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_ks_759_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_vs_760_);
v___x_765_ = v_reuseFailAlloc_777_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v_newNode_766_; size_t v___x_767_; uint8_t v___x_768_; 
v_newNode_766_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v___x_765_, v_x_707_, v_x_708_);
v___x_767_ = ((size_t)7ULL);
v___x_768_ = lean_usize_dec_le(v___x_767_, v_x_706_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_769_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_766_);
v___x_770_ = lean_unsigned_to_nat(4u);
v___x_771_ = lean_nat_dec_lt(v___x_769_, v___x_770_);
lean_dec(v___x_769_);
if (v___x_771_ == 0)
{
lean_object* v_ks_772_; lean_object* v_vs_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_ks_772_ = lean_ctor_get(v_newNode_766_, 0);
lean_inc_ref(v_ks_772_);
v_vs_773_ = lean_ctor_get(v_newNode_766_, 1);
lean_inc_ref(v_vs_773_);
lean_dec_ref(v_newNode_766_);
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0);
v___x_776_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_x_706_, v_ks_772_, v_vs_773_, v___x_774_, v___x_775_);
lean_dec_ref(v_vs_773_);
lean_dec_ref(v_ks_772_);
return v___x_776_;
}
else
{
return v_newNode_766_;
}
}
else
{
return v_newNode_766_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_704_ = stack[0].m_obj;
size_t v_x_705_ = stack[1].m_num;
size_t v_x_706_ = stack[2].m_num;
size_t v_x_707_ = stack[3].m_num;
lean_object* v_x_708_ = stack[4].m_obj;
lean_object* v_res_779_;
v_res_779_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_704_, v_x_705_, v_x_706_, v_x_707_, v_x_708_);
stack->m_obj
 = v_res_779_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(size_t v_depth_780_, lean_object* v_keys_781_, lean_object* v_vals_782_, lean_object* v_i_783_, lean_object* v_entries_784_){
_start:
{
lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_785_ = lean_array_get_size(v_keys_781_);
v___x_786_ = lean_nat_dec_lt(v_i_783_, v___x_785_);
if (v___x_786_ == 0)
{
lean_dec(v_i_783_);
return v_entries_784_;
}
else
{
lean_object* v_k_787_; lean_object* v_v_788_; size_t v___x_789_; uint64_t v___x_790_; size_t v_h_791_; size_t v___x_792_; lean_object* v___x_793_; size_t v___x_794_; size_t v___x_795_; size_t v___x_796_; size_t v_h_797_; lean_object* v___x_798_; size_t v___x_799_; lean_object* v___x_800_; 
v_k_787_ = lean_array_fget_borrowed(v_keys_781_, v_i_783_);
v_v_788_ = lean_array_fget_borrowed(v_vals_782_, v_i_783_);
v___x_789_ = lean_unbox_usize(v_k_787_);
v___x_790_ = l_Lean_Lsp_instHashableRpcRef_hash(v___x_789_);
v_h_791_ = lean_uint64_to_usize(v___x_790_);
v___x_792_ = ((size_t)5ULL);
v___x_793_ = lean_unsigned_to_nat(1u);
v___x_794_ = ((size_t)1ULL);
v___x_795_ = lean_usize_sub(v_depth_780_, v___x_794_);
v___x_796_ = lean_usize_mul(v___x_792_, v___x_795_);
v_h_797_ = lean_usize_shift_right(v_h_791_, v___x_796_);
v___x_798_ = lean_nat_add(v_i_783_, v___x_793_);
lean_dec(v_i_783_);
v___x_799_ = lean_unbox_usize(v_k_787_);
lean_inc(v_v_788_);
v___x_800_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_entries_784_, v_h_797_, v_depth_780_, v___x_799_, v_v_788_);
v_i_783_ = v___x_798_;
v_entries_784_ = v___x_800_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_780_ = stack[0].m_num;
lean_object* v_keys_781_ = stack[1].m_obj;
lean_object* v_vals_782_ = stack[2].m_obj;
lean_object* v_i_783_ = stack[3].m_obj;
lean_object* v_entries_784_ = stack[4].m_obj;
lean_object* v_res_802_;
v_res_802_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_depth_780_, v_keys_781_, v_vals_782_, v_i_783_, v_entries_784_);
stack->m_obj
 = v_res_802_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_803_, lean_object* v_keys_804_, lean_object* v_vals_805_, lean_object* v_i_806_, lean_object* v_entries_807_){
_start:
{
size_t v_depth_boxed_808_; lean_object* v_res_809_; 
v_depth_boxed_808_ = lean_unbox_usize(v_depth_803_);
lean_dec(v_depth_803_);
v_res_809_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_depth_boxed_808_, v_keys_804_, v_vals_805_, v_i_806_, v_entries_807_);
lean_dec_ref(v_vals_805_);
lean_dec_ref(v_keys_804_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___boxed(lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
size_t v_x_2407__boxed_815_; size_t v_x_2408__boxed_816_; size_t v_x_2409__boxed_817_; lean_object* v_res_818_; 
v_x_2407__boxed_815_ = lean_unbox_usize(v_x_811_);
lean_dec(v_x_811_);
v_x_2408__boxed_816_ = lean_unbox_usize(v_x_812_);
lean_dec(v_x_812_);
v_x_2409__boxed_817_ = lean_unbox_usize(v_x_813_);
lean_dec(v_x_813_);
v_res_818_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_810_, v_x_2407__boxed_815_, v_x_2408__boxed_816_, v_x_2409__boxed_817_, v_x_814_);
return v_res_818_;
}
}
lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(lean_object* v_x_819_, size_t v_x_820_, lean_object* v_x_821_){
_start:
{
uint64_t v___x_822_; size_t v___x_823_; size_t v___x_824_; lean_object* v___x_825_; 
v___x_822_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_820_);
v___x_823_ = lean_uint64_to_usize(v___x_822_);
v___x_824_ = ((size_t)1ULL);
v___x_825_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_819_, v___x_823_, v___x_824_, v_x_820_, v_x_821_);
return v___x_825_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_819_ = stack[0].m_obj;
size_t v_x_820_ = stack[1].m_num;
lean_object* v_x_821_ = stack[2].m_obj;
lean_object* v_res_826_;
v_res_826_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(v_x_819_, v_x_820_, v_x_821_);
stack->m_obj
 = v_res_826_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg___boxed(lean_object* v_x_827_, lean_object* v_x_828_, lean_object* v_x_829_){
_start:
{
size_t v_x_2661__boxed_830_; lean_object* v_res_831_; 
v_x_2661__boxed_830_ = lean_unbox_usize(v_x_828_);
lean_dec(v_x_828_);
v_res_831_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(v_x_827_, v_x_2661__boxed_830_, v_x_829_);
return v_res_831_;
}
}
lean_object* l_Lean_Server_rpcReleaseRef(size_t v_r_832_, lean_object* v_a_833_){
_start:
{
lean_object* v___y_835_; lean_object* v_aliveRefs_839_; lean_object* v_refsById_840_; size_t v_nextRef_841_; uint8_t v_wireFormat_842_; lean_object* v___x_843_; 
v_aliveRefs_839_ = lean_ctor_get(v_a_833_, 0);
v_refsById_840_ = lean_ctor_get(v_a_833_, 1);
v_nextRef_841_ = lean_ctor_get_usize(v_a_833_, 2);
v_wireFormat_842_ = lean_ctor_get_uint8(v_a_833_, sizeof(void*)*3);
v___x_843_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(v_aliveRefs_839_, v_r_832_);
if (lean_obj_tag(v___x_843_) == 1)
{
lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_871_; 
lean_inc_ref(v_refsById_840_);
lean_inc_ref(v_aliveRefs_839_);
v_isSharedCheck_871_ = !lean_is_exclusive(v_a_833_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; lean_object* v_unused_873_; 
v_unused_872_ = lean_ctor_get(v_a_833_, 1);
lean_dec(v_unused_872_);
v_unused_873_ = lean_ctor_get(v_a_833_, 0);
lean_dec(v_unused_873_);
v___x_845_ = v_a_833_;
v_isShared_846_ = v_isSharedCheck_871_;
goto v_resetjp_844_;
}
else
{
lean_dec(v_a_833_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_871_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v_val_847_; lean_object* v_obj_848_; size_t v_id_849_; lean_object* v_rc_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_870_; 
v_val_847_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_val_847_);
lean_dec_ref_known(v___x_843_, 1);
v_obj_848_ = lean_ctor_get(v_val_847_, 0);
v_id_849_ = lean_ctor_get_usize(v_val_847_, 2);
v_rc_850_ = lean_ctor_get(v_val_847_, 1);
v_isSharedCheck_870_ = !lean_is_exclusive(v_val_847_);
if (v_isSharedCheck_870_ == 0)
{
v___x_852_ = v_val_847_;
v_isShared_853_ = v_isSharedCheck_870_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_rc_850_);
lean_inc(v_obj_848_);
lean_dec(v_val_847_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_870_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_854_ = lean_unsigned_to_nat(1u);
v___x_855_ = lean_nat_sub(v_rc_850_, v___x_854_);
lean_dec(v_rc_850_);
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_nat_dec_eq(v___x_855_, v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_859_; 
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 1, v___x_855_);
v___x_859_ = v___x_852_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_obj_848_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v___x_855_);
lean_ctor_set_usize(v_reuseFailAlloc_864_, 2, v_id_849_);
v___x_859_ = v_reuseFailAlloc_864_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_860_; lean_object* v___x_862_; 
v___x_860_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(v_aliveRefs_839_, v_r_832_, v___x_859_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_860_);
v___x_862_ = v___x_845_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_refsById_840_);
lean_ctor_set_usize(v_reuseFailAlloc_863_, 2, v_nextRef_841_);
lean_ctor_set_uint8(v_reuseFailAlloc_863_, sizeof(void*)*3, v_wireFormat_842_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
v___y_835_ = v___x_862_;
goto v___jp_834_;
}
}
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
lean_dec(v___x_855_);
lean_del_object(v___x_852_);
lean_dec(v_obj_848_);
v___x_865_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(v_aliveRefs_839_, v_r_832_);
v___x_866_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(v_refsById_840_, v_id_849_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 1, v___x_866_);
lean_ctor_set(v___x_845_, 0, v___x_865_);
v___x_868_ = v___x_845_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_866_);
lean_ctor_set_usize(v_reuseFailAlloc_869_, 2, v_nextRef_841_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, sizeof(void*)*3, v_wireFormat_842_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
v___y_835_ = v___x_868_;
goto v___jp_834_;
}
}
}
}
}
else
{
uint8_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec(v___x_843_);
v___x_874_ = 0;
v___x_875_ = lean_box(v___x_874_);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v_a_833_);
return v___x_876_;
}
v___jp_834_:
{
uint8_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_836_ = 1;
v___x_837_ = lean_box(v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v___y_835_);
return v___x_838_;
}
}
}
LEAN_EXPORT void l_Lean_Server_rpcReleaseRef_0interp(lean_interpreter_value* stack)
{
size_t v_r_832_ = stack[0].m_num;
lean_object* v_a_833_ = stack[1].m_obj;
lean_object* v_res_877_;
v_res_877_ = l_Lean_Server_rpcReleaseRef(v_r_832_, v_a_833_);
stack->m_obj
 = v_res_877_;
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcReleaseRef___boxed(lean_object* v_r_878_, lean_object* v_a_879_){
_start:
{
size_t v_r_boxed_880_; lean_object* v_res_881_; 
v_r_boxed_880_ = lean_unbox_usize(v_r_878_);
lean_dec(v_r_878_);
v_res_881_ = l_Lean_Server_rpcReleaseRef(v_r_boxed_880_, v_a_879_);
return v_res_881_;
}
}
lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0(lean_object* v_00_u03b2_882_, lean_object* v_x_883_, size_t v_x_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(v_x_883_, v_x_884_);
return v___x_885_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_883_ = stack[1].m_obj;
size_t v_x_884_ = stack[2].m_num;
lean_object* v_res_886_;
v_res_886_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0(lean_box(0), v_x_883_, v_x_884_);
stack->m_obj
 = v_res_886_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___boxed(lean_object* v_00_u03b2_887_, lean_object* v_x_888_, lean_object* v_x_889_){
_start:
{
size_t v_x_2801__boxed_890_; lean_object* v_res_891_; 
v_x_2801__boxed_890_ = lean_unbox_usize(v_x_889_);
lean_dec(v_x_889_);
v_res_891_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0(v_00_u03b2_887_, v_x_888_, v_x_2801__boxed_890_);
lean_dec_ref(v_x_888_);
return v_res_891_;
}
}
lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1(lean_object* v_00_u03b2_892_, lean_object* v_x_893_, size_t v_x_894_, lean_object* v_x_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(v_x_893_, v_x_894_, v_x_895_);
return v___x_896_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_893_ = stack[1].m_obj;
size_t v_x_894_ = stack[2].m_num;
lean_object* v_x_895_ = stack[3].m_obj;
lean_object* v_res_897_;
v_res_897_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1(lean_box(0), v_x_893_, v_x_894_, v_x_895_);
stack->m_obj
 = v_res_897_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___boxed(lean_object* v_00_u03b2_898_, lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v_x_901_){
_start:
{
size_t v_x_2814__boxed_902_; lean_object* v_res_903_; 
v_x_2814__boxed_902_ = lean_unbox_usize(v_x_900_);
lean_dec(v_x_900_);
v_res_903_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1(v_00_u03b2_898_, v_x_899_, v_x_2814__boxed_902_, v_x_901_);
return v_res_903_;
}
}
lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2(lean_object* v_00_u03b2_904_, lean_object* v_x_905_, size_t v_x_906_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(v_x_905_, v_x_906_);
return v___x_907_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_905_ = stack[1].m_obj;
size_t v_x_906_ = stack[2].m_num;
lean_object* v_res_908_;
v_res_908_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2(lean_box(0), v_x_905_, v_x_906_);
stack->m_obj
 = v_res_908_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___boxed(lean_object* v_00_u03b2_909_, lean_object* v_x_910_, lean_object* v_x_911_){
_start:
{
size_t v_x_2832__boxed_912_; lean_object* v_res_913_; 
v_x_2832__boxed_912_ = lean_unbox_usize(v_x_911_);
lean_dec(v_x_911_);
v_res_913_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2(v_00_u03b2_909_, v_x_910_, v_x_2832__boxed_912_);
return v_res_913_;
}
}
lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3(lean_object* v_00_u03b2_914_, lean_object* v_x_915_, size_t v_x_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(v_x_915_, v_x_916_);
return v___x_917_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_915_ = stack[1].m_obj;
size_t v_x_916_ = stack[2].m_num;
lean_object* v_res_918_;
v_res_918_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3(lean_box(0), v_x_915_, v_x_916_);
stack->m_obj
 = v_res_918_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___boxed(lean_object* v_00_u03b2_919_, lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
size_t v_x_2845__boxed_922_; lean_object* v_res_923_; 
v_x_2845__boxed_922_ = lean_unbox_usize(v_x_921_);
lean_dec(v_x_921_);
v_res_923_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3(v_00_u03b2_919_, v_x_920_, v_x_2845__boxed_922_);
return v_res_923_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0(lean_object* v_00_u03b2_924_, lean_object* v_x_925_, size_t v_x_926_, size_t v_x_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_925_, v_x_926_, v_x_927_);
return v___x_928_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_925_ = stack[1].m_obj;
size_t v_x_926_ = stack[2].m_num;
size_t v_x_927_ = stack[3].m_num;
lean_object* v_res_929_;
v_res_929_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0(lean_box(0), v_x_925_, v_x_926_, v_x_927_);
stack->m_obj
 = v_res_929_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___boxed(lean_object* v_00_u03b2_930_, lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v_x_933_){
_start:
{
size_t v_x_2858__boxed_934_; size_t v_x_2859__boxed_935_; lean_object* v_res_936_; 
v_x_2858__boxed_934_ = lean_unbox_usize(v_x_932_);
lean_dec(v_x_932_);
v_x_2859__boxed_935_ = lean_unbox_usize(v_x_933_);
lean_dec(v_x_933_);
v_res_936_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0(v_00_u03b2_930_, v_x_931_, v_x_2858__boxed_934_, v_x_2859__boxed_935_);
lean_dec_ref(v_x_931_);
return v_res_936_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2(lean_object* v_00_u03b2_937_, lean_object* v_x_938_, size_t v_x_939_, size_t v_x_940_, size_t v_x_941_, lean_object* v_x_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_938_, v_x_939_, v_x_940_, v_x_941_, v_x_942_);
return v___x_943_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_938_ = stack[1].m_obj;
size_t v_x_939_ = stack[2].m_num;
size_t v_x_940_ = stack[3].m_num;
size_t v_x_941_ = stack[4].m_num;
lean_object* v_x_942_ = stack[5].m_obj;
lean_object* v_res_944_;
v_res_944_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2(lean_box(0), v_x_938_, v_x_939_, v_x_940_, v_x_941_, v_x_942_);
stack->m_obj
 = v_res_944_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___boxed(lean_object* v_00_u03b2_945_, lean_object* v_x_946_, lean_object* v_x_947_, lean_object* v_x_948_, lean_object* v_x_949_, lean_object* v_x_950_){
_start:
{
size_t v_x_2876__boxed_951_; size_t v_x_2877__boxed_952_; size_t v_x_2878__boxed_953_; lean_object* v_res_954_; 
v_x_2876__boxed_951_ = lean_unbox_usize(v_x_947_);
lean_dec(v_x_947_);
v_x_2877__boxed_952_ = lean_unbox_usize(v_x_948_);
lean_dec(v_x_948_);
v_x_2878__boxed_953_ = lean_unbox_usize(v_x_949_);
lean_dec(v_x_949_);
v_res_954_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2(v_00_u03b2_945_, v_x_946_, v_x_2876__boxed_951_, v_x_2877__boxed_952_, v_x_2878__boxed_953_, v_x_950_);
return v_res_954_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4(lean_object* v_00_u03b2_955_, lean_object* v_x_956_, size_t v_x_957_, size_t v_x_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_x_956_, v_x_957_, v_x_958_);
return v___x_959_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_956_ = stack[1].m_obj;
size_t v_x_957_ = stack[2].m_num;
size_t v_x_958_ = stack[3].m_num;
lean_object* v_res_960_;
v_res_960_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4(lean_box(0), v_x_956_, v_x_957_, v_x_958_);
stack->m_obj
 = v_res_960_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___boxed(lean_object* v_00_u03b2_961_, lean_object* v_x_962_, lean_object* v_x_963_, lean_object* v_x_964_){
_start:
{
size_t v_x_2904__boxed_965_; size_t v_x_2905__boxed_966_; lean_object* v_res_967_; 
v_x_2904__boxed_965_ = lean_unbox_usize(v_x_963_);
lean_dec(v_x_963_);
v_x_2905__boxed_966_ = lean_unbox_usize(v_x_964_);
lean_dec(v_x_964_);
v_res_967_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4(v_00_u03b2_961_, v_x_962_, v_x_2904__boxed_965_, v_x_2905__boxed_966_);
return v_res_967_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6(lean_object* v_00_u03b2_968_, lean_object* v_x_969_, size_t v_x_970_, size_t v_x_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_969_, v_x_970_, v_x_971_);
return v___x_972_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_969_ = stack[1].m_obj;
size_t v_x_970_ = stack[2].m_num;
size_t v_x_971_ = stack[3].m_num;
lean_object* v_res_973_;
v_res_973_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6(lean_box(0), v_x_969_, v_x_970_, v_x_971_);
stack->m_obj
 = v_res_973_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___boxed(lean_object* v_00_u03b2_974_, lean_object* v_x_975_, lean_object* v_x_976_, lean_object* v_x_977_){
_start:
{
size_t v_x_2922__boxed_978_; size_t v_x_2923__boxed_979_; lean_object* v_res_980_; 
v_x_2922__boxed_978_ = lean_unbox_usize(v_x_976_);
lean_dec(v_x_976_);
v_x_2923__boxed_979_ = lean_unbox_usize(v_x_977_);
lean_dec(v_x_977_);
v_res_980_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6(v_00_u03b2_974_, v_x_975_, v_x_2922__boxed_978_, v_x_2923__boxed_979_);
return v_res_980_;
}
}
lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_981_, lean_object* v_keys_982_, lean_object* v_vals_983_, lean_object* v_heq_984_, lean_object* v_i_985_, size_t v_k_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(v_keys_982_, v_vals_983_, v_i_985_, v_k_986_);
return v___x_987_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_982_ = stack[1].m_obj;
lean_object* v_vals_983_ = stack[2].m_obj;
lean_object* v_i_985_ = stack[4].m_obj;
size_t v_k_986_ = stack[5].m_num;
lean_object* v_res_988_;
v_res_988_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1(lean_box(0), v_keys_982_, v_vals_983_, lean_box(0), v_i_985_, v_k_986_);
stack->m_obj
 = v_res_988_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_989_, lean_object* v_keys_990_, lean_object* v_vals_991_, lean_object* v_heq_992_, lean_object* v_i_993_, lean_object* v_k_994_){
_start:
{
size_t v_k_boxed_995_; lean_object* v_res_996_; 
v_k_boxed_995_ = lean_unbox_usize(v_k_994_);
lean_dec(v_k_994_);
v_res_996_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1(v_00_u03b2_989_, v_keys_990_, v_vals_991_, v_heq_992_, v_i_993_, v_k_boxed_995_);
lean_dec_ref(v_vals_991_);
lean_dec_ref(v_keys_990_);
return v_res_996_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_997_, lean_object* v_n_998_, size_t v_k_999_, lean_object* v_v_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v_n_998_, v_k_999_, v_v_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_998_ = stack[1].m_obj;
size_t v_k_999_ = stack[2].m_num;
lean_object* v_v_1000_ = stack[3].m_obj;
lean_object* v_res_1002_;
v_res_1002_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4(lean_box(0), v_n_998_, v_k_999_, v_v_1000_);
stack->m_obj
 = v_res_1002_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1003_, lean_object* v_n_1004_, lean_object* v_k_1005_, lean_object* v_v_1006_){
_start:
{
size_t v_k_boxed_1007_; lean_object* v_res_1008_; 
v_k_boxed_1007_ = lean_unbox_usize(v_k_1005_);
lean_dec(v_k_1005_);
v_res_1008_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4(v_00_u03b2_1003_, v_n_1004_, v_k_boxed_1007_, v_v_1006_);
return v_res_1008_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1009_, size_t v_depth_1010_, lean_object* v_keys_1011_, lean_object* v_vals_1012_, lean_object* v_heq_1013_, lean_object* v_i_1014_, lean_object* v_entries_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_depth_1010_, v_keys_1011_, v_vals_1012_, v_i_1014_, v_entries_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1010_ = stack[1].m_num;
lean_object* v_keys_1011_ = stack[2].m_obj;
lean_object* v_vals_1012_ = stack[3].m_obj;
lean_object* v_i_1014_ = stack[5].m_obj;
lean_object* v_entries_1015_ = stack[6].m_obj;
lean_object* v_res_1017_;
v_res_1017_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5(lean_box(0), v_depth_1010_, v_keys_1011_, v_vals_1012_, lean_box(0), v_i_1014_, v_entries_1015_);
stack->m_obj
 = v_res_1017_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1018_, lean_object* v_depth_1019_, lean_object* v_keys_1020_, lean_object* v_vals_1021_, lean_object* v_heq_1022_, lean_object* v_i_1023_, lean_object* v_entries_1024_){
_start:
{
size_t v_depth_boxed_1025_; lean_object* v_res_1026_; 
v_depth_boxed_1025_ = lean_unbox_usize(v_depth_1019_);
lean_dec(v_depth_1019_);
v_res_1026_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5(v_00_u03b2_1018_, v_depth_boxed_1025_, v_keys_1020_, v_vals_1021_, v_heq_1022_, v_i_1023_, v_entries_1024_);
lean_dec_ref(v_vals_1021_);
lean_dec_ref(v_keys_1020_);
return v_res_1026_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_1027_, lean_object* v_x_1028_, lean_object* v_x_1029_, size_t v_x_1030_, lean_object* v_x_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_x_1028_, v_x_1029_, v_x_1030_, v_x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1028_ = stack[1].m_obj;
lean_object* v_x_1029_ = stack[2].m_obj;
size_t v_x_1030_ = stack[3].m_num;
lean_object* v_x_1031_ = stack[4].m_obj;
lean_object* v_res_1033_;
v_res_1033_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7(lean_box(0), v_x_1028_, v_x_1029_, v_x_1030_, v_x_1031_);
stack->m_obj
 = v_res_1033_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_, lean_object* v_x_1037_, lean_object* v_x_1038_){
_start:
{
size_t v_x_2950__boxed_1039_; lean_object* v_res_1040_; 
v_x_2950__boxed_1039_ = lean_unbox_usize(v_x_1037_);
lean_dec(v_x_1037_);
v_res_1040_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7(v_00_u03b2_1034_, v_x_1035_, v_x_1036_, v_x_2950__boxed_1039_, v_x_1038_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__0(lean_object* v_inst_1041_, lean_object* v_a_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_apply_1(v_inst_1041_, v_a_1042_);
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v___y_1043_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1(lean_object* v_inst_1046_, lean_object* v___x_1047_, lean_object* v___x_1048_, lean_object* v_j_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_205__overap_1052_; lean_object* v___x_1053_; 
v___x_1051_ = lean_apply_1(v_inst_1046_, v_j_1049_);
v___x_205__overap_1052_ = l_MonadExcept_ofExcept___redArg(v___x_1047_, v___x_1048_, v___x_1051_);
lean_inc_ref(v___y_1050_);
v___x_1053_ = lean_apply_1(v___x_205__overap_1052_, v___y_1050_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1___boxed(lean_object* v_inst_1054_, lean_object* v___x_1055_, lean_object* v___x_1056_, lean_object* v_j_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1(v_inst_1054_, v___x_1055_, v___x_1056_, v_j_1057_, v___y_1058_);
lean_dec_ref(v___y_1058_);
return v_res_1059_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9));
v___x_1080_ = l_ReaderT_instMonad___redArg(v___x_1079_);
return v___x_1080_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___f_1082_; 
v___x_1081_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___f_1082_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1082_, 0, v___x_1081_);
return v___f_1082_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___f_1084_; 
v___x_1083_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___f_1084_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_1084_, 0, v___x_1083_);
return v___f_1084_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___f_1086_; 
v___x_1085_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___f_1086_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_1086_, 0, v___x_1085_);
return v___f_1086_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___f_1088_; 
v___x_1087_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___f_1088_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_1088_, 0, v___x_1087_);
return v___f_1088_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1090_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_1090_, 0, lean_box(0));
lean_closure_set(v___x_1090_, 1, lean_box(0));
lean_closure_set(v___x_1090_, 2, v___x_1089_);
return v___x_1090_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16(void){
_start:
{
lean_object* v___f_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___f_1091_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11);
v___x_1092_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15);
v___x_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
lean_ctor_set(v___x_1093_, 1, v___f_1091_);
return v___x_1093_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1095_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_1095_, 0, lean_box(0));
lean_closure_set(v___x_1095_, 1, lean_box(0));
lean_closure_set(v___x_1095_, 2, v___x_1094_);
return v___x_1095_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18(void){
_start:
{
lean_object* v___f_1096_; lean_object* v___f_1097_; lean_object* v___f_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___f_1096_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14);
v___f_1097_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13);
v___f_1098_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12);
v___x_1099_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17);
v___x_1100_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16);
v___x_1101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
lean_ctor_set(v___x_1101_, 1, v___x_1099_);
lean_ctor_set(v___x_1101_, 2, v___f_1098_);
lean_ctor_set(v___x_1101_, 3, v___f_1097_);
lean_ctor_set(v___x_1101_, 4, v___f_1096_);
return v___x_1101_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1103_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_1103_, 0, lean_box(0));
lean_closure_set(v___x_1103_, 1, lean_box(0));
lean_closure_set(v___x_1103_, 2, v___x_1102_);
return v___x_1103_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19);
v___x_1105_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18);
v___x_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
lean_ctor_set(v___x_1106_, 1, v___x_1104_);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1108_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch), 6, 3);
lean_closure_set(v___x_1108_, 0, lean_box(0));
lean_closure_set(v___x_1108_, 1, lean_box(0));
lean_closure_set(v___x_1108_, 2, v___x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg(lean_object* v_inst_1109_, lean_object* v_inst_1110_){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v_toApplicative_1113_; lean_object* v_toPure_1114_; lean_object* v___f_1115_; lean_object* v___f_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___f_1120_; lean_object* v___x_1121_; 
v___x_1111_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1112_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20);
v_toApplicative_1113_ = lean_ctor_get(v___x_1111_, 0);
v_toPure_1114_ = lean_ctor_get(v_toApplicative_1113_, 1);
v___f_1115_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1115_, 0, v_inst_1110_);
lean_inc(v_toPure_1114_);
v___f_1116_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptTOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1116_, 0, v_toPure_1114_);
v___x_1117_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___f_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_1118_);
v___f_1120_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1120_, 0, v_inst_1109_);
lean_closure_set(v___f_1120_, 1, v___x_1112_);
lean_closure_set(v___f_1120_, 2, v___x_1119_);
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___f_1115_);
lean_ctor_set(v___x_1121_, 1, v___f_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson(lean_object* v_00_u03b1_1122_, lean_object* v_inst_1123_, lean_object* v_inst_1124_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg(v_inst_1123_, v_inst_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg___lam__0(lean_object* v_inst_1126_, lean_object* v___x_1127_, lean_object* v_v_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_fst_1131_; lean_object* v_snd_1132_; 
if (lean_obj_tag(v_v_1128_) == 0)
{
lean_object* v___x_1135_; 
lean_dec_ref(v_inst_1126_);
v___x_1135_ = lean_box(0);
v_fst_1131_ = v___x_1135_;
v_snd_1132_ = v___y_1129_;
goto v___jp_1130_;
}
else
{
lean_object* v_rpcEncode_1136_; lean_object* v_val_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1147_; 
v_rpcEncode_1136_ = lean_ctor_get(v_inst_1126_, 0);
lean_inc_ref(v_rpcEncode_1136_);
lean_dec_ref(v_inst_1126_);
v_val_1137_ = lean_ctor_get(v_v_1128_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_v_1128_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1139_ = v_v_1128_;
v_isShared_1140_ = v_isSharedCheck_1147_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_val_1137_);
lean_dec(v_v_1128_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1147_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; lean_object* v_fst_1142_; lean_object* v_snd_1143_; lean_object* v___x_1145_; 
v___x_1141_ = lean_apply_2(v_rpcEncode_1136_, v_val_1137_, v___y_1129_);
v_fst_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_fst_1142_);
v_snd_1143_ = lean_ctor_get(v___x_1141_, 1);
lean_inc(v_snd_1143_);
lean_dec_ref(v___x_1141_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v_fst_1142_);
v___x_1145_ = v___x_1139_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_fst_1142_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
v_fst_1131_ = v___x_1145_;
v_snd_1132_ = v_snd_1143_;
goto v___jp_1130_;
}
}
}
v___jp_1130_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = l_Lean_Option_toJson___redArg(v___x_1127_, v_fst_1131_);
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
lean_ctor_set(v___x_1134_, 1, v_snd_1132_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg___lam__1(lean_object* v___f_1150_, lean_object* v_inst_1151_, lean_object* v_j_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_Option_fromJson_x3f___redArg(v___f_1150_, v_j_1152_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec_ref(v_inst_1151_);
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
else
{
lean_object* v_a_1163_; 
v_a_1163_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1154_, 1);
if (lean_obj_tag(v_a_1163_) == 0)
{
lean_object* v___x_1164_; 
lean_dec_ref(v_inst_1151_);
v___x_1164_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___lam__1___closed__0));
return v___x_1164_;
}
else
{
lean_object* v_rpcDecode_1165_; lean_object* v_val_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1190_; 
v_rpcDecode_1165_ = lean_ctor_get(v_inst_1151_, 1);
lean_inc_ref(v_rpcDecode_1165_);
lean_dec_ref(v_inst_1151_);
v_val_1166_ = lean_ctor_get(v_a_1163_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_a_1163_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1168_ = v_a_1163_;
v_isShared_1169_ = v_isSharedCheck_1190_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_val_1166_);
lean_dec(v_a_1163_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1190_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; 
lean_inc_ref(v___y_1153_);
v___x_1170_ = lean_apply_2(v_rpcDecode_1165_, v_val_1166_, v___y_1153_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_del_object(v___x_1168_);
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1189_; 
v_a_1179_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1181_ = v___x_1170_;
v_isShared_1182_ = v_isSharedCheck_1189_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1170_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1189_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v_a_1179_);
v___x_1184_ = v___x_1168_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1186_; 
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1184_);
v___x_1186_ = v___x_1181_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg___lam__1___boxed(lean_object* v___f_1191_, lean_object* v_inst_1192_, lean_object* v_j_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_Server_instRpcEncodableOption___redArg___lam__1(v___f_1191_, v_inst_1192_, v_j_1193_, v___y_1194_);
lean_dec_ref(v___y_1194_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg(lean_object* v_inst_1198_){
_start:
{
lean_object* v___x_1199_; lean_object* v___f_1200_; lean_object* v___f_1201_; lean_object* v___f_1202_; lean_object* v___x_1203_; 
v___x_1199_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__0));
lean_inc_ref(v_inst_1198_);
v___f_1200_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOption___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1200_, 0, v_inst_1198_);
lean_closure_set(v___f_1200_, 1, v___x_1199_);
v___f_1201_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__1));
v___f_1202_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOption___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1202_, 0, v___f_1201_);
lean_closure_set(v___f_1202_, 1, v_inst_1198_);
v___x_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___f_1200_);
lean_ctor_set(v___x_1203_, 1, v___f_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption(lean_object* v_00_u03b1_1204_, lean_object* v_inst_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_Server_instRpcEncodableOption___redArg(v_inst_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__0(lean_object* v_inst_1207_, lean_object* v___x_1208_, lean_object* v___x_1209_, lean_object* v_a_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_rpcEncode_1212_; size_t v_sz_1213_; size_t v___x_1214_; lean_object* v___x_651__overap_1215_; lean_object* v___x_1216_; lean_object* v_fst_1217_; lean_object* v_snd_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1226_; 
v_rpcEncode_1212_ = lean_ctor_get(v_inst_1207_, 0);
lean_inc_ref(v_rpcEncode_1212_);
lean_dec_ref(v_inst_1207_);
v_sz_1213_ = lean_array_size(v_a_1210_);
v___x_1214_ = ((size_t)0ULL);
v___x_651__overap_1215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1208_, v_rpcEncode_1212_, v_sz_1213_, v___x_1214_, v_a_1210_);
v___x_1216_ = lean_apply_1(v___x_651__overap_1215_, v___y_1211_);
v_fst_1217_ = lean_ctor_get(v___x_1216_, 0);
v_snd_1218_ = lean_ctor_get(v___x_1216_, 1);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1220_ = v___x_1216_;
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_snd_1218_);
lean_inc(v_fst_1217_);
lean_dec(v___x_1216_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1222_ = l_Lean_Array_toJson___redArg(v___x_1209_, v_fst_1217_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1222_);
v___x_1224_ = v___x_1220_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_snd_1218_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__1(lean_object* v___f_1227_, lean_object* v_inst_1228_, lean_object* v___x_1229_, lean_object* v_b_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_Array_fromJson_x3f___redArg(v___f_1227_, v_b_1230_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec_ref(v___x_1229_);
lean_dec_ref(v_inst_1228_);
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v_rpcDecode_1242_; size_t v_sz_1243_; size_t v___x_1244_; lean_object* v___x_665__overap_1245_; lean_object* v___x_1246_; 
v_a_1241_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1241_);
lean_dec_ref_known(v___x_1232_, 1);
v_rpcDecode_1242_ = lean_ctor_get(v_inst_1228_, 1);
lean_inc_ref(v_rpcDecode_1242_);
lean_dec_ref(v_inst_1228_);
v_sz_1243_ = lean_array_size(v_a_1241_);
v___x_1244_ = ((size_t)0ULL);
v___x_665__overap_1245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1229_, v_rpcDecode_1242_, v_sz_1243_, v___x_1244_, v_a_1241_);
lean_inc_ref(v___y_1231_);
v___x_1246_ = lean_apply_1(v___x_665__overap_1245_, v___y_1231_);
return v___x_1246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__1___boxed(lean_object* v___f_1247_, lean_object* v_inst_1248_, lean_object* v___x_1249_, lean_object* v_b_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_Server_instRpcEncodableArray___redArg___lam__1(v___f_1247_, v_inst_1248_, v___x_1249_, v_b_1250_, v___y_1251_);
lean_dec_ref(v___y_1251_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg(lean_object* v_inst_1279_){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___f_1282_; lean_object* v___x_1283_; lean_object* v___f_1284_; lean_object* v___f_1285_; lean_object* v___x_1286_; 
v___x_1280_ = ((lean_object*)(l_Lean_Server_instRpcEncodableArray___redArg___closed__9));
v___x_1281_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__0));
lean_inc_ref(v_inst_1279_);
v___f_1282_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableArray___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1282_, 0, v_inst_1279_);
lean_closure_set(v___f_1282_, 1, v___x_1280_);
lean_closure_set(v___f_1282_, 2, v___x_1281_);
v___x_1283_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20);
v___f_1284_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__1));
v___f_1285_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableArray___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1285_, 0, v___f_1284_);
lean_closure_set(v___f_1285_, 1, v_inst_1279_);
lean_closure_set(v___f_1285_, 2, v___x_1283_);
v___x_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___f_1282_);
lean_ctor_set(v___x_1286_, 1, v___f_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray(lean_object* v_00_u03b1_1287_, lean_object* v_inst_1288_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Lean_Server_instRpcEncodableArray___redArg(v_inst_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg___lam__0(lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v___x_1292_, lean_object* v_x_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_fst_1295_; lean_object* v_snd_1296_; lean_object* v_rpcEncode_1297_; lean_object* v___x_1298_; lean_object* v_fst_1299_; lean_object* v_snd_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1319_; 
v_fst_1295_ = lean_ctor_get(v_x_1293_, 0);
lean_inc(v_fst_1295_);
v_snd_1296_ = lean_ctor_get(v_x_1293_, 1);
lean_inc(v_snd_1296_);
lean_dec_ref(v_x_1293_);
v_rpcEncode_1297_ = lean_ctor_get(v_inst_1290_, 0);
lean_inc_ref(v_rpcEncode_1297_);
lean_dec_ref(v_inst_1290_);
v___x_1298_ = lean_apply_2(v_rpcEncode_1297_, v_fst_1295_, v___y_1294_);
v_fst_1299_ = lean_ctor_get(v___x_1298_, 0);
v_snd_1300_ = lean_ctor_get(v___x_1298_, 1);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1302_ = v___x_1298_;
v_isShared_1303_ = v_isSharedCheck_1319_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_snd_1300_);
lean_inc(v_fst_1299_);
lean_dec(v___x_1298_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1319_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v_rpcEncode_1304_; lean_object* v___x_1305_; lean_object* v_fst_1306_; lean_object* v_snd_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1318_; 
v_rpcEncode_1304_ = lean_ctor_get(v_inst_1291_, 0);
lean_inc_ref(v_rpcEncode_1304_);
lean_dec_ref(v_inst_1291_);
v___x_1305_ = lean_apply_2(v_rpcEncode_1304_, v_snd_1296_, v_snd_1300_);
v_fst_1306_ = lean_ctor_get(v___x_1305_, 0);
v_snd_1307_ = lean_ctor_get(v___x_1305_, 1);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1309_ = v___x_1305_;
v_isShared_1310_ = v_isSharedCheck_1318_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_snd_1307_);
lean_inc(v_fst_1306_);
lean_dec(v___x_1305_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1318_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 1, v_fst_1306_);
lean_ctor_set(v___x_1309_, 0, v_fst_1299_);
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_fst_1299_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_fst_1306_);
v___x_1312_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
lean_inc_ref(v___x_1292_);
v___x_1313_ = l_Lean_Prod_toJson___redArg(v___x_1292_, v___x_1292_, v___x_1312_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 1, v_snd_1307_);
lean_ctor_set(v___x_1302_, 0, v___x_1313_);
v___x_1315_ = v___x_1302_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_snd_1307_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg___lam__1(lean_object* v___f_1320_, lean_object* v_inst_1321_, lean_object* v_inst_1322_, lean_object* v_j_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v___x_1325_; 
lean_inc_ref(v___f_1320_);
v___x_1325_ = l_Lean_Prod_fromJson_x3f___redArg(v___f_1320_, v___f_1320_, v_j_1323_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec_ref(v_inst_1322_);
lean_dec_ref(v_inst_1321_);
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1325_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1325_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
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
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
else
{
lean_object* v_a_1334_; lean_object* v_fst_1335_; lean_object* v_snd_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1372_; 
v_a_1334_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1325_, 1);
v_fst_1335_ = lean_ctor_get(v_a_1334_, 0);
v_snd_1336_ = lean_ctor_get(v_a_1334_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_a_1334_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1338_ = v_a_1334_;
v_isShared_1339_ = v_isSharedCheck_1372_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_snd_1336_);
lean_inc(v_fst_1335_);
lean_dec(v_a_1334_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1372_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v_rpcDecode_1340_; lean_object* v___x_1341_; 
v_rpcDecode_1340_ = lean_ctor_get(v_inst_1321_, 1);
lean_inc_ref(v_rpcDecode_1340_);
lean_dec_ref(v_inst_1321_);
lean_inc_ref(v___y_1324_);
v___x_1341_ = lean_apply_2(v_rpcDecode_1340_, v_fst_1335_, v___y_1324_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_del_object(v___x_1338_);
lean_dec(v_snd_1336_);
lean_dec_ref(v_inst_1322_);
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v_rpcDecode_1351_; lean_object* v___x_1352_; 
v_a_1350_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1341_, 1);
v_rpcDecode_1351_ = lean_ctor_get(v_inst_1322_, 1);
lean_inc_ref(v_rpcDecode_1351_);
lean_dec_ref(v_inst_1322_);
lean_inc_ref(v___y_1324_);
v___x_1352_ = lean_apply_2(v_rpcDecode_1351_, v_snd_1336_, v___y_1324_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec(v_a_1350_);
lean_del_object(v___x_1338_);
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1371_; 
v_a_1361_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1363_ = v___x_1352_;
v_isShared_1364_ = v_isSharedCheck_1371_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1352_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1371_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 1, v_a_1361_);
lean_ctor_set(v___x_1338_, 0, v_a_1350_);
v___x_1366_ = v___x_1338_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1350_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1368_; 
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1366_);
v___x_1368_ = v___x_1363_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg___lam__1___boxed(lean_object* v___f_1373_, lean_object* v_inst_1374_, lean_object* v_inst_1375_, lean_object* v_j_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Lean_Server_instRpcEncodableProd___redArg___lam__1(v___f_1373_, v_inst_1374_, v_inst_1375_, v_j_1376_, v___y_1377_);
lean_dec_ref(v___y_1377_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg(lean_object* v_inst_1379_, lean_object* v_inst_1380_){
_start:
{
lean_object* v___x_1381_; lean_object* v___f_1382_; lean_object* v___f_1383_; lean_object* v___f_1384_; lean_object* v___x_1385_; 
v___x_1381_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__0));
lean_inc_ref(v_inst_1380_);
lean_inc_ref(v_inst_1379_);
v___f_1382_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableProd___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1382_, 0, v_inst_1379_);
lean_closure_set(v___f_1382_, 1, v_inst_1380_);
lean_closure_set(v___f_1382_, 2, v___x_1381_);
v___f_1383_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__1));
v___f_1384_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableProd___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1384_, 0, v___f_1383_);
lean_closure_set(v___f_1384_, 1, v_inst_1379_);
lean_closure_set(v___f_1384_, 2, v_inst_1380_);
v___x_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___f_1382_);
lean_ctor_set(v___x_1385_, 1, v___f_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd(lean_object* v_00_u03b1_1386_, lean_object* v_00_u03b2_1387_, lean_object* v_inst_1388_, lean_object* v_inst_1389_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_Server_instRpcEncodableProd___redArg(v_inst_1388_, v_inst_1389_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__0(lean_object* v_inst_1391_, lean_object* v_fn_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v_rpcEncode_1394_; lean_object* v___x_1395_; lean_object* v_fst_1396_; lean_object* v_snd_1397_; lean_object* v___x_1398_; 
v_rpcEncode_1394_ = lean_ctor_get(v_inst_1391_, 0);
lean_inc_ref(v_rpcEncode_1394_);
lean_dec_ref(v_inst_1391_);
v___x_1395_ = lean_apply_1(v_fn_1392_, v___y_1393_);
v_fst_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_fst_1396_);
v_snd_1397_ = lean_ctor_get(v___x_1395_, 1);
lean_inc(v_snd_1397_);
lean_dec_ref(v___x_1395_);
v___x_1398_ = lean_apply_2(v_rpcEncode_1394_, v_fst_1396_, v_snd_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1(lean_object* v_inst_1399_, lean_object* v___x_1400_, lean_object* v_j_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_rpcDecode_1403_; lean_object* v___x_1404_; 
v_rpcDecode_1403_ = lean_ctor_get(v_inst_1399_, 1);
lean_inc_ref(v_rpcDecode_1403_);
lean_dec_ref(v_inst_1399_);
lean_inc_ref(v___y_1402_);
v___x_1404_ = lean_apply_2(v_rpcDecode_1403_, v_j_1401_, v___y_1402_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec_ref(v___x_1400_);
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
v___x_1417_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 5);
lean_closure_set(v___x_1417_, 0, lean_box(0));
lean_closure_set(v___x_1417_, 1, lean_box(0));
lean_closure_set(v___x_1417_, 2, v___x_1400_);
lean_closure_set(v___x_1417_, 3, lean_box(0));
lean_closure_set(v___x_1417_, 4, v_a_1413_);
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
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1___boxed(lean_object* v_inst_1422_, lean_object* v___x_1423_, lean_object* v_j_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1(v_inst_1422_, v___x_1423_, v_j_1424_, v___y_1425_);
lean_dec_ref(v___y_1425_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg(lean_object* v_inst_1427_){
_start:
{
lean_object* v___f_1428_; lean_object* v___x_1429_; lean_object* v___f_1430_; lean_object* v___x_1431_; 
lean_inc_ref(v_inst_1427_);
v___f_1428_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1428_, 0, v_inst_1427_);
v___x_1429_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9));
v___f_1430_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1430_, 0, v_inst_1427_);
lean_closure_set(v___f_1430_, 1, v___x_1429_);
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___f_1428_);
lean_ctor_set(v___x_1431_, 1, v___f_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore(lean_object* v_00_u03b1_1432_, lean_object* v_inst_1433_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg(v_inst_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(lean_object* v_inst_1435_, lean_object* v_r_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v___x_1438_; lean_object* v_fst_1439_; lean_object* v_snd_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1459_; 
v___x_1438_ = l_Lean_Server_rpcStoreRef___redArg(v_inst_1435_, v_r_1436_, v_a_1437_);
v_fst_1439_ = lean_ctor_get(v___x_1438_, 0);
v_snd_1440_ = lean_ctor_get(v___x_1438_, 1);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1442_ = v___x_1438_;
v_isShared_1443_ = v_isSharedCheck_1459_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_snd_1440_);
lean_inc(v_fst_1439_);
lean_dec(v___x_1438_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1459_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___y_1445_; uint8_t v_wireFormat_1456_; 
v_wireFormat_1456_ = lean_ctor_get_uint8(v_snd_1440_, sizeof(void*)*3);
if (v_wireFormat_1456_ == 0)
{
lean_object* v___x_1457_; 
v___x_1457_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0));
v___y_1445_ = v___x_1457_;
goto v___jp_1444_;
}
else
{
lean_object* v___x_1458_; 
v___x_1458_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1));
v___y_1445_ = v___x_1458_;
goto v___jp_1444_;
}
v___jp_1444_:
{
size_t v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1446_ = lean_unbox_usize(v_fst_1439_);
lean_dec(v_fst_1439_);
v___x_1447_ = lean_usize_to_nat(v___x_1446_);
v___x_1448_ = l_Lean_bignumToJson(v___x_1447_);
lean_inc_ref(v___y_1445_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 1, v___x_1448_);
lean_ctor_set(v___x_1442_, 0, v___y_1445_);
v___x_1450_ = v___x_1442_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___y_1445_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1451_ = lean_box(0);
v___x_1452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1450_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = l_Lean_Json_mkObj(v___x_1452_);
lean_dec_ref_known(v___x_1452_, 2);
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
lean_ctor_set(v___x_1454_, 1, v_snd_1440_);
return v___x_1454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg___boxed(lean_object* v_inst_1460_, lean_object* v_r_1461_, lean_object* v_a_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(v_inst_1460_, v_r_1461_, v_a_1462_);
lean_dec_ref(v_r_1461_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode(lean_object* v_00_u03b1_1464_, lean_object* v_inst_1465_, lean_object* v_r_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(v_inst_1465_, v_r_1466_, v_a_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___boxed(lean_object* v_00_u03b1_1469_, lean_object* v_inst_1470_, lean_object* v_r_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode(v_00_u03b1_1469_, v_inst_1470_, v_r_1471_, v_a_1472_);
lean_dec_ref(v_r_1471_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(lean_object* v_inst_1475_, lean_object* v_j_1476_, lean_object* v_a_1477_){
_start:
{
uint8_t v_wireFormat_1478_; lean_object* v___x_1479_; lean_object* v___y_1481_; 
v_wireFormat_1478_ = lean_ctor_get_uint8(v_a_1477_, sizeof(void*)*3);
v___x_1479_ = ((lean_object*)(l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg___closed__0));
if (v_wireFormat_1478_ == 0)
{
lean_object* v___x_1494_; 
v___x_1494_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0));
v___y_1481_ = v___x_1494_;
goto v___jp_1480_;
}
else
{
lean_object* v___x_1495_; 
v___x_1495_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1));
v___y_1481_ = v___x_1495_;
goto v___jp_1480_;
}
v___jp_1480_:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1476_, v___x_1479_, v___y_1481_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec(v_inst_1475_);
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
lean_object* v_a_1491_; size_t v___x_1492_; lean_object* v___x_1493_; 
v_a_1491_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1491_);
lean_dec_ref_known(v___x_1482_, 1);
v___x_1492_ = lean_unbox_usize(v_a_1491_);
lean_dec(v_a_1491_);
v___x_1493_ = l_Lean_Server_rpcGetRef___redArg(v_inst_1475_, v___x_1492_, v_a_1477_);
return v___x_1493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg___boxed(lean_object* v_inst_1496_, lean_object* v_j_1497_, lean_object* v_a_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v_inst_1496_, v_j_1497_, v_a_1498_);
lean_dec_ref(v_a_1498_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode(lean_object* v_00_u03b1_1500_, lean_object* v_inst_1501_, lean_object* v_j_1502_, lean_object* v_a_1503_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v_inst_1501_, v_j_1502_, v_a_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___boxed(lean_object* v_00_u03b1_1505_, lean_object* v_inst_1506_, lean_object* v_j_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode(v_00_u03b1_1505_, v_inst_1506_, v_j_1507_, v_a_1508_);
lean_dec_ref(v_a_1508_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName___redArg(lean_object* v_inst_1510_){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_inc(v_inst_1510_);
v___x_1511_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___boxed), 4, 2);
lean_closure_set(v___x_1511_, 0, lean_box(0));
lean_closure_set(v___x_1511_, 1, v_inst_1510_);
v___x_1512_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___boxed), 4, 2);
lean_closure_set(v___x_1512_, 0, lean_box(0));
lean_closure_set(v___x_1512_, 1, v_inst_1510_);
v___x_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1511_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName(lean_object* v_00_u03b1_1514_, lean_object* v_inst_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName___redArg(v_inst_1515_);
return v___x_1516_;
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
