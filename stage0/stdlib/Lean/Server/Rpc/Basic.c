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
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_USize_fromJson_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
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
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_toJson___redArg(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Prod_toJson___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instFromJsonJson___lam__0(lean_object*);
lean_object* l_Prod_fromJson_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_bignumToJson(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
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
lean_object* lean_st_mk_ref(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcRef_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcRef_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "p"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lsp"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__2_value;
static const lean_string_object l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "RpcRef"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__3_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__4_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__4_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(83, 126, 80, 30, 68, 142, 243, 208)}};
static const lean_object* l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__5;
static const lean_string_object l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__7;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 153, 146, 175, 179, 220, 230, 134)}};
static const lean_object* l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__10;
static const lean_string_object l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__11 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__11_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__12;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcRef_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonRpcRef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonRpcRef_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonRpcRef___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcRef___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonRpcRef = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcRef___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonRpcRef_toJson_spec__0(lean_object*, lean_object*);
static const lean_array_object l_Lean_Lsp_instToJsonRpcRef_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_instToJsonRpcRef_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRpcRef_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcRef_toJson(size_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcRef_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonRpcRef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonRpcRef_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonRpcRef___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRpcRef___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonRpcRef = (const lean_object*)&l_Lean_Lsp_instToJsonRpcRef___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToStringRpcRef___lam__0(size_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToStringRpcRef___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToStringRpcRef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToStringRpcRef___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToStringRpcRef___closed__0 = (const lean_object*)&l_Lean_Lsp_instToStringRpcRef___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToStringRpcRef = (const lean_object*)&l_Lean_Lsp_instToStringRpcRef___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_initFn___boxed__const__1_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(1ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Server_initFn___boxed__const__1_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_initFn___boxed__const__1_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2____boxed(lean_object*);
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
static const lean_closure_object l_Lean_Server_instRpcEncodableOption___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Server_instRpcEncodableOption___redArg___closed__0 = (const lean_object*)&l_Lean_Server_instRpcEncodableOption___redArg___closed__0_value;
static const lean_closure_object l_Lean_Server_instRpcEncodableOption___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instRpcEncodableOption___redArg___closed__1 = (const lean_object*)&l_Lean_Server_instRpcEncodableOption___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcRef_fromJson_spec__0(lean_object* v_j_26_, lean_object* v_k_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = l_Lean_Json_getObjValD(v_j_26_, v_k_27_);
v___x_29_ = l_USize_fromJson_x3f(v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcRef_fromJson_spec__0___boxed(lean_object* v_j_30_, lean_object* v_k_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcRef_fromJson_spec__0(v_j_30_, v_k_31_);
lean_dec_ref(v_k_31_);
return v_res_32_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__5(void){
_start:
{
uint8_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = 1;
v___x_42_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__4));
v___x_43_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_42_, v___x_41_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__7(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_45_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__6));
v___x_46_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__5);
v___x_47_ = lean_string_append(v___x_46_, v___x_45_);
return v___x_47_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__9(void){
_start:
{
uint8_t v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = 1;
v___x_51_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__8));
v___x_52_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_51_, v___x_50_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__10(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__9, &l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__9);
v___x_54_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__7);
v___x_55_ = lean_string_append(v___x_54_, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__12(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__11));
v___x_58_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__10, &l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__10);
v___x_59_ = lean_string_append(v___x_58_, v___x_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcRef_fromJson(lean_object* v_json_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__0));
v___x_62_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcRef_fromJson_spec__0(v_json_60_, v___x_61_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_72_; 
v_a_63_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_72_ == 0)
{
v___x_65_ = v___x_62_;
v_isShared_66_ = v_isSharedCheck_72_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v___x_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_72_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_67_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__12, &l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__12);
v___x_68_ = lean_string_append(v___x_67_, v_a_63_);
lean_dec(v_a_63_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v___x_68_);
v___x_70_ = v___x_65_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_68_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
else
{
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
v_a_73_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_80_ == 0)
{
v___x_75_ = v___x_62_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_62_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
lean_ctor_set_tag(v___x_75_, 0);
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_a_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
else
{
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_88_; 
v_a_81_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_88_ == 0)
{
v___x_83_ = v___x_62_;
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_62_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_81_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonRpcRef_toJson_spec__0(lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
if (lean_obj_tag(v_a_91_) == 0)
{
lean_object* v___x_93_; 
v___x_93_ = lean_array_to_list(v_a_92_);
return v___x_93_;
}
else
{
lean_object* v_head_94_; lean_object* v_tail_95_; lean_object* v___x_96_; 
v_head_94_ = lean_ctor_get(v_a_91_, 0);
lean_inc(v_head_94_);
v_tail_95_ = lean_ctor_get(v_a_91_, 1);
lean_inc(v_tail_95_);
lean_dec_ref(v_a_91_);
v___x_96_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_92_, v_head_94_);
v_a_91_ = v_tail_95_;
v_a_92_ = v___x_96_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcRef_toJson(size_t v_x_100_){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_101_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcRef_fromJson___closed__0));
v___x_102_ = lean_usize_to_nat(v_x_100_);
v___x_103_ = l_Lean_bignumToJson(v___x_102_);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_101_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = lean_box(0);
v___x_106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_104_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v___x_105_);
v___x_108_ = ((lean_object*)(l_Lean_Lsp_instToJsonRpcRef_toJson___closed__0));
v___x_109_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonRpcRef_toJson_spec__0(v___x_107_, v___x_108_);
v___x_110_ = l_Lean_Json_mkObj(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcRef_toJson___boxed(lean_object* v_x_111_){
_start:
{
size_t v_x_65__boxed_112_; lean_object* v_res_113_; 
v_x_65__boxed_112_ = lean_unbox_usize(v_x_111_);
lean_dec(v_x_111_);
v_res_113_ = l_Lean_Lsp_instToJsonRpcRef_toJson(v_x_65__boxed_112_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToStringRpcRef___lam__0(size_t v_r_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_usize_to_nat(v_r_116_);
v___x_118_ = l_Nat_reprFast(v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToStringRpcRef___lam__0___boxed(lean_object* v_r_119_){
_start:
{
size_t v_r_boxed_120_; lean_object* v_res_121_; 
v_r_boxed_120_ = lean_unbox_usize(v_r_119_);
lean_dec(v_r_119_);
v_res_121_ = l_Lean_Lsp_instToStringRpcRef___lam__0(v_r_boxed_120_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef_default___redArg(lean_object* v_inst_124_){
_start:
{
size_t v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_usize_once(&l_Lean_Lsp_instInhabitedRpcRef_default___closed__0, &l_Lean_Lsp_instInhabitedRpcRef_default___closed__0_once, _init_l_Lean_Lsp_instInhabitedRpcRef_default___closed__0);
v___x_126_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_126_, 0, v_inst_124_);
lean_ctor_set_usize(v___x_126_, 1, v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef_default(lean_object* v_a_127_, lean_object* v_inst_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_Server_instInhabitedWithRpcRef_default___redArg(v_inst_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef___redArg(lean_object* v_inst_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_Server_instInhabitedWithRpcRef_default___redArg(v_inst_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef(lean_object* v_a_132_, lean_object* v_inst_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Server_instInhabitedWithRpcRef_default___redArg(v_inst_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = ((lean_object*)(l_Lean_Server_initFn___boxed__const__1_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_));
v___x_139_ = lean_st_mk_ref(v___x_138_);
v___x_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2____boxed(lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_();
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_WithRpcRef_mk___redArg(lean_object* v_val_143_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; size_t v___x_153_; 
v___x_145_ = l_Lean_Server_freshWithRpcRefId;
v___x_146_ = lean_st_ref_take(v___x_145_);
v___x_147_ = ((size_t)1ULL);
v___x_148_ = lean_unbox_usize(v___x_146_);
v___x_149_ = lean_usize_add(v___x_148_, v___x_147_);
v___x_150_ = lean_box_usize(v___x_149_);
v___x_151_ = lean_st_ref_set(v___x_145_, v___x_150_);
v___x_152_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_152_, 0, v_val_143_);
v___x_153_ = lean_unbox_usize(v___x_146_);
lean_dec(v___x_146_);
lean_ctor_set_usize(v___x_152_, 1, v___x_153_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_WithRpcRef_mk___redArg___boxed(lean_object* v_val_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Server_WithRpcRef_mk___redArg(v_val_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_WithRpcRef_mk(lean_object* v_00_u03b1_157_, lean_object* v_val_158_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_Server_WithRpcRef_mk___redArg(v_val_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_WithRpcRef_mk___boxed(lean_object* v_00_u03b1_161_, lean_object* v_val_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Server_WithRpcRef_mk(v_00_u03b1_161_, v_val_162_);
return v_res_164_;
}
}
static lean_object* _init_l_Lean_Server_rpcStoreRef___redArg___closed__1(void){
_start:
{
lean_object* v___x_166_; lean_object* v___f_167_; 
v___x_166_ = lean_alloc_closure((void*)(l_instDecidableEqUSize___boxed), 2, 0);
v___f_167_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_167_, 0, v___x_166_);
return v___f_167_;
}
}
static lean_object* _init_l_Lean_Server_rpcStoreRef___redArg___closed__5(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_171_ = ((lean_object*)(l_Lean_Server_rpcStoreRef___redArg___closed__4));
v___x_172_ = lean_unsigned_to_nat(15u);
v___x_173_ = lean_unsigned_to_nat(103u);
v___x_174_ = ((lean_object*)(l_Lean_Server_rpcStoreRef___redArg___closed__3));
v___x_175_ = ((lean_object*)(l_Lean_Server_rpcStoreRef___redArg___closed__2));
v___x_176_ = l_mkPanicMessageWithDecl(v___x_175_, v___x_174_, v___x_173_, v___x_172_, v___x_171_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_Server_rpcStoreRef___redArg___boxed__const__1(void){
_start:
{
size_t v___x_177_; lean_object* v___x_178_; 
v___x_177_ = l_Lean_Lsp_instInhabitedRpcRef_default;
v___x_178_ = lean_box_usize(v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcStoreRef___redArg(lean_object* v_inst_179_, lean_object* v_obj_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_aliveRefs_182_; lean_object* v_refsById_183_; size_t v_nextRef_184_; lean_object* v_val_185_; size_t v_id_186_; lean_object* v___f_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___f_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_aliveRefs_182_ = lean_ctor_get(v_a_181_, 0);
v_refsById_183_ = lean_ctor_get(v_a_181_, 1);
v_nextRef_184_ = lean_ctor_get_usize(v_a_181_, 2);
v_val_185_ = lean_ctor_get(v_obj_180_, 0);
v_id_186_ = lean_ctor_get_usize(v_obj_180_, 1);
v___f_187_ = ((lean_object*)(l_Lean_Server_rpcStoreRef___redArg___closed__0));
v___x_188_ = ((lean_object*)(l_Lean_Lsp_instBEqRpcRef___closed__0));
v___x_189_ = ((lean_object*)(l_Lean_Lsp_instHashableRpcRef___closed__0));
v___f_190_ = lean_obj_once(&l_Lean_Server_rpcStoreRef___redArg___closed__1, &l_Lean_Server_rpcStoreRef___redArg___closed__1_once, _init_l_Lean_Server_rpcStoreRef___redArg___closed__1);
v___x_191_ = lean_box_usize(v_id_186_);
lean_inc_ref(v_refsById_183_);
v___x_192_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_190_, v___f_187_, v_refsById_183_, v___x_191_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_211_; 
lean_inc_ref(v_refsById_183_);
lean_inc_ref(v_aliveRefs_182_);
v_isSharedCheck_211_ = !lean_is_exclusive(v_a_181_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; lean_object* v_unused_213_; 
v_unused_212_ = lean_ctor_get(v_a_181_, 1);
lean_dec(v_unused_212_);
v_unused_213_ = lean_ctor_get(v_a_181_, 0);
lean_dec(v_unused_213_);
v___x_194_ = v_a_181_;
v_isShared_195_ = v_isSharedCheck_211_;
goto v_resetjp_193_;
}
else
{
lean_dec(v_a_181_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_211_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; size_t v___x_204_; size_t v___x_205_; lean_object* v___x_207_; 
lean_inc(v_val_185_);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v_inst_179_);
lean_ctor_set(v___x_196_, 1, v_val_185_);
v___x_197_ = lean_unsigned_to_nat(1u);
v___x_198_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
lean_ctor_set_usize(v___x_198_, 2, v_id_186_);
v___x_199_ = lean_box_usize(v_nextRef_184_);
v___x_200_ = l_Lean_PersistentHashMap_insert___redArg(v___x_188_, v___x_189_, v_aliveRefs_182_, v___x_199_, v___x_198_);
v___x_201_ = lean_box_usize(v_id_186_);
v___x_202_ = lean_box_usize(v_nextRef_184_);
v___x_203_ = l_Lean_PersistentHashMap_insert___redArg(v___f_190_, v___f_187_, v_refsById_183_, v___x_201_, v___x_202_);
v___x_204_ = ((size_t)1ULL);
v___x_205_ = lean_usize_add(v_nextRef_184_, v___x_204_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 1, v___x_203_);
lean_ctor_set(v___x_194_, 0, v___x_200_);
v___x_207_ = v___x_194_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v___x_203_);
v___x_207_ = v_reuseFailAlloc_210_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
lean_ctor_set_usize(v___x_207_, 2, v___x_205_);
v___x_208_ = lean_box_usize(v_nextRef_184_);
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v___x_207_);
return v___x_209_;
}
}
}
else
{
lean_object* v_val_214_; lean_object* v___x_215_; 
lean_dec(v_inst_179_);
v_val_214_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_val_214_);
lean_dec_ref(v___x_192_);
lean_inc(v_val_214_);
lean_inc_ref(v_aliveRefs_182_);
v___x_215_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_188_, v___x_189_, v_aliveRefs_182_, v_val_214_);
if (lean_obj_tag(v___x_215_) == 1)
{
lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_237_; 
lean_inc_ref(v_refsById_183_);
lean_inc_ref(v_aliveRefs_182_);
v_isSharedCheck_237_ = !lean_is_exclusive(v_a_181_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; lean_object* v_unused_239_; 
v_unused_238_ = lean_ctor_get(v_a_181_, 1);
lean_dec(v_unused_238_);
v_unused_239_ = lean_ctor_get(v_a_181_, 0);
lean_dec(v_unused_239_);
v___x_217_ = v_a_181_;
v_isShared_218_ = v_isSharedCheck_237_;
goto v_resetjp_216_;
}
else
{
lean_dec(v_a_181_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_237_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v_val_219_; lean_object* v_obj_220_; size_t v_id_221_; lean_object* v_rc_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_236_; 
v_val_219_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_val_219_);
lean_dec_ref(v___x_215_);
v_obj_220_ = lean_ctor_get(v_val_219_, 0);
v_id_221_ = lean_ctor_get_usize(v_val_219_, 2);
v_rc_222_ = lean_ctor_get(v_val_219_, 1);
v_isSharedCheck_236_ = !lean_is_exclusive(v_val_219_);
if (v_isSharedCheck_236_ == 0)
{
v___x_224_ = v_val_219_;
v_isShared_225_ = v_isSharedCheck_236_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_rc_222_);
lean_inc(v_obj_220_);
lean_dec(v_val_219_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_236_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_226_ = lean_unsigned_to_nat(1u);
v___x_227_ = lean_nat_add(v_rc_222_, v___x_226_);
lean_dec(v_rc_222_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v___x_227_);
v___x_229_ = v___x_224_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_obj_220_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v___x_227_);
lean_ctor_set_usize(v_reuseFailAlloc_235_, 2, v_id_221_);
v___x_229_ = v_reuseFailAlloc_235_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; lean_object* v___x_232_; 
lean_inc(v_val_214_);
v___x_230_ = l_Lean_PersistentHashMap_insert___redArg(v___x_188_, v___x_189_, v_aliveRefs_182_, v_val_214_, v___x_229_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_230_);
v___x_232_ = v___x_217_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_refsById_183_);
lean_ctor_set_usize(v_reuseFailAlloc_234_, 2, v_nextRef_184_);
v___x_232_ = v_reuseFailAlloc_234_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; 
v___x_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_233_, 0, v_val_214_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
return v___x_233_;
}
}
}
}
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec(v___x_215_);
lean_dec(v_val_214_);
v___x_240_ = lean_obj_once(&l_Lean_Server_rpcStoreRef___redArg___closed__5, &l_Lean_Server_rpcStoreRef___redArg___closed__5_once, _init_l_Lean_Server_rpcStoreRef___redArg___closed__5);
v___x_241_ = l_Lean_Server_rpcStoreRef___redArg___boxed__const__1;
v___x_242_ = l_panic___redArg(v___x_241_, v___x_240_);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v_a_181_);
return v___x_243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcStoreRef___redArg___boxed(lean_object* v_inst_244_, lean_object* v_obj_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Server_rpcStoreRef___redArg(v_inst_244_, v_obj_245_, v_a_246_);
lean_dec_ref(v_obj_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcStoreRef(lean_object* v_00_u03b1_248_, lean_object* v_inst_249_, lean_object* v_obj_250_, lean_object* v_a_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_Server_rpcStoreRef___redArg(v_inst_249_, v_obj_250_, v_a_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcStoreRef___boxed(lean_object* v_00_u03b1_253_, lean_object* v_inst_254_, lean_object* v_obj_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Server_rpcStoreRef(v_00_u03b1_253_, v_inst_254_, v_obj_255_, v_a_256_);
lean_dec_ref(v_obj_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcGetRef___redArg(lean_object* v_inst_265_, size_t v_r_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_aliveRefs_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_aliveRefs_268_ = lean_ctor_get(v_a_267_, 0);
lean_inc_ref(v_aliveRefs_268_);
lean_dec_ref(v_a_267_);
v___x_269_ = ((lean_object*)(l_Lean_Lsp_instBEqRpcRef___closed__0));
v___x_270_ = ((lean_object*)(l_Lean_Lsp_instHashableRpcRef___closed__0));
v___x_271_ = lean_box_usize(v_r_266_);
v___x_272_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_269_, v___x_270_, v_aliveRefs_268_, v___x_271_);
if (lean_obj_tag(v___x_272_) == 1)
{
lean_object* v_val_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_310_; 
v_val_273_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_310_ == 0)
{
v___x_275_ = v___x_272_;
v_isShared_276_ = v_isSharedCheck_310_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_val_273_);
lean_dec(v___x_272_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_310_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v_obj_277_; size_t v_id_278_; lean_object* v___x_279_; 
v_obj_277_ = lean_ctor_get(v_val_273_, 0);
lean_inc(v_obj_277_);
v_id_278_ = lean_ctor_get_usize(v_val_273_, 2);
lean_dec(v_val_273_);
v___x_279_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_obj_277_, v_inst_265_);
if (lean_obj_tag(v___x_279_) == 1)
{
lean_object* v_val_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_288_; 
lean_dec(v_obj_277_);
lean_del_object(v___x_275_);
lean_dec(v_inst_265_);
v_val_280_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_288_ == 0)
{
v___x_282_ = v___x_279_;
v_isShared_283_ = v_isSharedCheck_288_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_val_280_);
lean_dec(v___x_279_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_288_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_284_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_284_, 0, v_val_280_);
lean_ctor_set_usize(v___x_284_, 1, v_id_278_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_284_);
v___x_286_ = v___x_282_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
lean_dec(v___x_279_);
v___x_289_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__0));
v___x_290_ = lean_usize_to_nat(v_r_266_);
v___x_291_ = l_Nat_reprFast(v___x_290_);
v___x_292_ = lean_string_append(v___x_289_, v___x_291_);
lean_dec_ref(v___x_291_);
v___x_293_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__1));
v___x_294_ = lean_string_append(v___x_292_, v___x_293_);
v___x_295_ = 1;
v___x_296_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_inst_265_, v___x_295_);
v___x_297_ = lean_string_append(v___x_294_, v___x_296_);
lean_dec_ref(v___x_296_);
v___x_298_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__2));
v___x_299_ = lean_string_append(v___x_297_, v___x_298_);
v___x_300_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__3));
v___x_301_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_obj_277_);
lean_dec(v_obj_277_);
v___x_302_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_301_, v___x_295_);
v___x_303_ = lean_string_append(v___x_300_, v___x_302_);
lean_dec_ref(v___x_302_);
v___x_304_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__4));
v___x_305_ = lean_string_append(v___x_303_, v___x_304_);
v___x_306_ = lean_string_append(v___x_299_, v___x_305_);
lean_dec_ref(v___x_305_);
if (v_isShared_276_ == 0)
{
lean_ctor_set_tag(v___x_275_, 0);
lean_ctor_set(v___x_275_, 0, v___x_306_);
v___x_308_ = v___x_275_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v___x_272_);
lean_dec(v_inst_265_);
v___x_311_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__5));
v___x_312_ = lean_usize_to_nat(v_r_266_);
v___x_313_ = l_Nat_reprFast(v___x_312_);
v___x_314_ = lean_string_append(v___x_311_, v___x_313_);
lean_dec_ref(v___x_313_);
v___x_315_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__6));
v___x_316_ = lean_string_append(v___x_314_, v___x_315_);
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcGetRef___redArg___boxed(lean_object* v_inst_318_, lean_object* v_r_319_, lean_object* v_a_320_){
_start:
{
size_t v_r_boxed_321_; lean_object* v_res_322_; 
v_r_boxed_321_ = lean_unbox_usize(v_r_319_);
lean_dec(v_r_319_);
v_res_322_ = l_Lean_Server_rpcGetRef___redArg(v_inst_318_, v_r_boxed_321_, v_a_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcGetRef(lean_object* v_00_u03b1_323_, lean_object* v_inst_324_, size_t v_r_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Server_rpcGetRef___redArg(v_inst_324_, v_r_325_, v_a_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcGetRef___boxed(lean_object* v_00_u03b1_328_, lean_object* v_inst_329_, lean_object* v_r_330_, lean_object* v_a_331_){
_start:
{
size_t v_r_boxed_332_; lean_object* v_res_333_; 
v_r_boxed_332_ = lean_unbox_usize(v_r_330_);
lean_dec(v_r_330_);
v_res_333_ = l_Lean_Server_rpcGetRef(v_00_u03b1_328_, v_inst_329_, v_r_boxed_332_, v_a_331_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11(lean_object* v_xs_334_, size_t v_v_335_, lean_object* v_i_336_){
_start:
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = lean_array_get_size(v_xs_334_);
v___x_338_ = lean_nat_dec_lt(v_i_336_, v___x_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
lean_dec(v_i_336_);
v___x_339_ = lean_box(0);
return v___x_339_;
}
else
{
lean_object* v___x_340_; size_t v___x_341_; uint8_t v___x_342_; 
v___x_340_ = lean_array_fget_borrowed(v_xs_334_, v_i_336_);
v___x_341_ = lean_unbox_usize(v___x_340_);
v___x_342_ = lean_usize_dec_eq(v___x_341_, v_v_335_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_unsigned_to_nat(1u);
v___x_344_ = lean_nat_add(v_i_336_, v___x_343_);
lean_dec(v_i_336_);
v_i_336_ = v___x_344_;
goto _start;
}
else
{
lean_object* v___x_346_; 
v___x_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_346_, 0, v_i_336_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11___boxed(lean_object* v_xs_347_, lean_object* v_v_348_, lean_object* v_i_349_){
_start:
{
size_t v_v_boxed_350_; lean_object* v_res_351_; 
v_v_boxed_350_ = lean_unbox_usize(v_v_348_);
lean_dec(v_v_348_);
v_res_351_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11(v_xs_347_, v_v_boxed_350_, v_i_349_);
lean_dec_ref(v_xs_347_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8(lean_object* v_xs_352_, size_t v_v_353_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11(v_xs_352_, v_v_353_, v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8___boxed(lean_object* v_xs_356_, lean_object* v_v_357_){
_start:
{
size_t v_v_boxed_358_; lean_object* v_res_359_; 
v_v_boxed_358_ = lean_unbox_usize(v_v_357_);
lean_dec(v_v_357_);
v_res_359_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8(v_xs_356_, v_v_boxed_358_);
lean_dec_ref(v_xs_356_);
return v_res_359_;
}
}
static size_t _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_360_; size_t v___x_361_; size_t v___x_362_; 
v___x_360_ = ((size_t)5ULL);
v___x_361_ = ((size_t)1ULL);
v___x_362_ = lean_usize_shift_left(v___x_361_, v___x_360_);
return v___x_362_;
}
}
static size_t _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_363_; size_t v___x_364_; size_t v___x_365_; 
v___x_363_ = ((size_t)1ULL);
v___x_364_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__0);
v___x_365_ = lean_usize_sub(v___x_364_, v___x_363_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(lean_object* v_x_366_, size_t v_x_367_, size_t v_x_368_){
_start:
{
if (lean_obj_tag(v_x_366_) == 0)
{
lean_object* v_es_369_; lean_object* v___x_370_; size_t v___x_371_; size_t v___x_372_; size_t v___x_373_; lean_object* v_j_374_; lean_object* v_entry_375_; 
v_es_369_ = lean_ctor_get(v_x_366_, 0);
v___x_370_ = lean_box(2);
v___x_371_ = ((size_t)5ULL);
v___x_372_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1);
v___x_373_ = lean_usize_land(v_x_367_, v___x_372_);
v_j_374_ = lean_usize_to_nat(v___x_373_);
v_entry_375_ = lean_array_get(v___x_370_, v_es_369_, v_j_374_);
switch(lean_obj_tag(v_entry_375_))
{
case 0:
{
lean_object* v_key_376_; size_t v___x_377_; uint8_t v___x_378_; 
v_key_376_ = lean_ctor_get(v_entry_375_, 0);
lean_inc(v_key_376_);
lean_dec_ref(v_entry_375_);
v___x_377_ = lean_unbox_usize(v_key_376_);
lean_dec(v_key_376_);
v___x_378_ = lean_usize_dec_eq(v_x_368_, v___x_377_);
if (v___x_378_ == 0)
{
lean_dec(v_j_374_);
return v_x_366_;
}
else
{
lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_386_; 
lean_inc_ref(v_es_369_);
v_isSharedCheck_386_ = !lean_is_exclusive(v_x_366_);
if (v_isSharedCheck_386_ == 0)
{
lean_object* v_unused_387_; 
v_unused_387_ = lean_ctor_get(v_x_366_, 0);
lean_dec(v_unused_387_);
v___x_380_ = v_x_366_;
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
else
{
lean_dec(v_x_366_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_382_ = lean_array_set(v_es_369_, v_j_374_, v___x_370_);
lean_dec(v_j_374_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___x_382_);
v___x_384_ = v___x_380_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
case 1:
{
lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_421_; 
lean_inc_ref(v_es_369_);
v_isSharedCheck_421_ = !lean_is_exclusive(v_x_366_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v_x_366_, 0);
lean_dec(v_unused_422_);
v___x_389_ = v_x_366_;
v_isShared_390_ = v_isSharedCheck_421_;
goto v_resetjp_388_;
}
else
{
lean_dec(v_x_366_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_421_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v_node_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_420_; 
v_node_391_ = lean_ctor_get(v_entry_375_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v_entry_375_);
if (v_isSharedCheck_420_ == 0)
{
v___x_393_ = v_entry_375_;
v_isShared_394_ = v_isSharedCheck_420_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_node_391_);
lean_dec(v_entry_375_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_420_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v_entries_395_; size_t v___x_396_; lean_object* v_newNode_397_; lean_object* v___x_398_; 
v_entries_395_ = lean_array_set(v_es_369_, v_j_374_, v___x_370_);
v___x_396_ = lean_usize_shift_right(v_x_367_, v___x_371_);
v_newNode_397_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_node_391_, v___x_396_, v_x_368_);
lean_inc_ref(v_newNode_397_);
v___x_398_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_397_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v___x_400_; 
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v_newNode_397_);
v___x_400_ = v___x_393_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_newNode_397_);
v___x_400_ = v_reuseFailAlloc_405_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = lean_array_set(v_entries_395_, v_j_374_, v___x_400_);
lean_dec(v_j_374_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_401_);
v___x_403_ = v___x_389_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
else
{
lean_object* v_val_406_; lean_object* v_fst_407_; lean_object* v_snd_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_419_; 
lean_dec_ref(v_newNode_397_);
lean_del_object(v___x_393_);
v_val_406_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_val_406_);
lean_dec_ref(v___x_398_);
v_fst_407_ = lean_ctor_get(v_val_406_, 0);
v_snd_408_ = lean_ctor_get(v_val_406_, 1);
v_isSharedCheck_419_ = !lean_is_exclusive(v_val_406_);
if (v_isSharedCheck_419_ == 0)
{
v___x_410_ = v_val_406_;
v_isShared_411_ = v_isSharedCheck_419_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_snd_408_);
lean_inc(v_fst_407_);
lean_dec(v_val_406_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_419_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_fst_407_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_snd_408_);
v___x_413_ = v_reuseFailAlloc_418_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = lean_array_set(v_entries_395_, v_j_374_, v___x_413_);
lean_dec(v_j_374_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_414_);
v___x_416_ = v___x_389_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_374_);
return v_x_366_;
}
}
}
else
{
lean_object* v_ks_423_; lean_object* v_vs_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_438_; 
v_ks_423_ = lean_ctor_get(v_x_366_, 0);
v_vs_424_ = lean_ctor_get(v_x_366_, 1);
v_isSharedCheck_438_ = !lean_is_exclusive(v_x_366_);
if (v_isSharedCheck_438_ == 0)
{
v___x_426_ = v_x_366_;
v_isShared_427_ = v_isSharedCheck_438_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_vs_424_);
lean_inc(v_ks_423_);
lean_dec(v_x_366_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_438_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; 
v___x_428_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8(v_ks_423_, v_x_368_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v___x_430_; 
if (v_isShared_427_ == 0)
{
v___x_430_ = v___x_426_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_ks_423_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_vs_424_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
else
{
lean_object* v_val_432_; lean_object* v_keys_x27_433_; lean_object* v_vals_x27_434_; lean_object* v___x_436_; 
v_val_432_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_val_432_);
lean_dec_ref(v___x_428_);
lean_inc(v_val_432_);
v_keys_x27_433_ = l_Array_eraseIdx___redArg(v_ks_423_, v_val_432_);
v_vals_x27_434_ = l_Array_eraseIdx___redArg(v_vs_424_, v_val_432_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v_vals_x27_434_);
lean_ctor_set(v___x_426_, 0, v_keys_x27_433_);
v___x_436_ = v___x_426_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_keys_x27_433_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_vals_x27_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___boxed(lean_object* v_x_439_, lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
size_t v_x_1710__boxed_442_; size_t v_x_1711__boxed_443_; lean_object* v_res_444_; 
v_x_1710__boxed_442_ = lean_unbox_usize(v_x_440_);
lean_dec(v_x_440_);
v_x_1711__boxed_443_ = lean_unbox_usize(v_x_441_);
lean_dec(v_x_441_);
v_res_444_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_x_439_, v_x_1710__boxed_442_, v_x_1711__boxed_443_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(lean_object* v_x_445_, size_t v_x_446_){
_start:
{
uint64_t v___x_447_; size_t v_h_448_; lean_object* v___x_449_; 
v___x_447_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_446_);
v_h_448_ = lean_uint64_to_usize(v___x_447_);
v___x_449_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_x_445_, v_h_448_, v_x_446_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg___boxed(lean_object* v_x_450_, lean_object* v_x_451_){
_start:
{
size_t v_x_1854__boxed_452_; lean_object* v_res_453_; 
v_x_1854__boxed_452_ = lean_unbox_usize(v_x_451_);
lean_dec(v_x_451_);
v_res_453_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(v_x_450_, v_x_1854__boxed_452_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_454_, lean_object* v_vals_455_, lean_object* v_i_456_, size_t v_k_457_){
_start:
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = lean_array_get_size(v_keys_454_);
v___x_459_ = lean_nat_dec_lt(v_i_456_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; 
lean_dec(v_i_456_);
v___x_460_ = lean_box(0);
return v___x_460_;
}
else
{
lean_object* v_k_x27_461_; size_t v___x_462_; uint8_t v___x_463_; 
v_k_x27_461_ = lean_array_fget_borrowed(v_keys_454_, v_i_456_);
v___x_462_ = lean_unbox_usize(v_k_x27_461_);
v___x_463_ = lean_usize_dec_eq(v_k_457_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_unsigned_to_nat(1u);
v___x_465_ = lean_nat_add(v_i_456_, v___x_464_);
lean_dec(v_i_456_);
v_i_456_ = v___x_465_;
goto _start;
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_array_fget_borrowed(v_vals_455_, v_i_456_);
lean_dec(v_i_456_);
lean_inc(v___x_467_);
v___x_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
return v___x_468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_469_, lean_object* v_vals_470_, lean_object* v_i_471_, lean_object* v_k_472_){
_start:
{
size_t v_k_boxed_473_; lean_object* v_res_474_; 
v_k_boxed_473_ = lean_unbox_usize(v_k_472_);
lean_dec(v_k_472_);
v_res_474_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(v_keys_469_, v_vals_470_, v_i_471_, v_k_boxed_473_);
lean_dec_ref(v_vals_470_);
lean_dec_ref(v_keys_469_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(lean_object* v_x_475_, size_t v_x_476_, size_t v_x_477_){
_start:
{
if (lean_obj_tag(v_x_475_) == 0)
{
lean_object* v_es_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_500_; 
v_es_478_ = lean_ctor_get(v_x_475_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v_x_475_);
if (v_isSharedCheck_500_ == 0)
{
v___x_480_ = v_x_475_;
v_isShared_481_ = v_isSharedCheck_500_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_es_478_);
lean_dec(v_x_475_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_500_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; size_t v___x_483_; size_t v___x_484_; size_t v___x_485_; lean_object* v_j_486_; lean_object* v___x_487_; 
v___x_482_ = lean_box(2);
v___x_483_ = ((size_t)5ULL);
v___x_484_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1);
v___x_485_ = lean_usize_land(v_x_476_, v___x_484_);
v_j_486_ = lean_usize_to_nat(v___x_485_);
v___x_487_ = lean_array_get(v___x_482_, v_es_478_, v_j_486_);
lean_dec(v_j_486_);
lean_dec_ref(v_es_478_);
switch(lean_obj_tag(v___x_487_))
{
case 0:
{
lean_object* v_key_488_; lean_object* v_val_489_; size_t v___x_490_; uint8_t v___x_491_; 
v_key_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_key_488_);
v_val_489_ = lean_ctor_get(v___x_487_, 1);
lean_inc(v_val_489_);
lean_dec_ref(v___x_487_);
v___x_490_ = lean_unbox_usize(v_key_488_);
lean_dec(v_key_488_);
v___x_491_ = lean_usize_dec_eq(v_x_477_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; 
lean_dec(v_val_489_);
lean_del_object(v___x_480_);
v___x_492_ = lean_box(0);
return v___x_492_;
}
else
{
lean_object* v___x_494_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set_tag(v___x_480_, 1);
lean_ctor_set(v___x_480_, 0, v_val_489_);
v___x_494_ = v___x_480_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_val_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
case 1:
{
lean_object* v_node_496_; size_t v___x_497_; 
lean_del_object(v___x_480_);
v_node_496_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_node_496_);
lean_dec_ref(v___x_487_);
v___x_497_ = lean_usize_shift_right(v_x_476_, v___x_483_);
v_x_475_ = v_node_496_;
v_x_476_ = v___x_497_;
goto _start;
}
default: 
{
lean_object* v___x_499_; 
lean_del_object(v___x_480_);
v___x_499_ = lean_box(0);
return v___x_499_;
}
}
}
}
else
{
lean_object* v_ks_501_; lean_object* v_vs_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_ks_501_ = lean_ctor_get(v_x_475_, 0);
lean_inc_ref(v_ks_501_);
v_vs_502_ = lean_ctor_get(v_x_475_, 1);
lean_inc_ref(v_vs_502_);
lean_dec_ref(v_x_475_);
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(v_ks_501_, v_vs_502_, v___x_503_, v_x_477_);
lean_dec_ref(v_vs_502_);
lean_dec_ref(v_ks_501_);
return v___x_504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg___boxed(lean_object* v_x_505_, lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
size_t v_x_1890__boxed_508_; size_t v_x_1891__boxed_509_; lean_object* v_res_510_; 
v_x_1890__boxed_508_ = lean_unbox_usize(v_x_506_);
lean_dec(v_x_506_);
v_x_1891__boxed_509_ = lean_unbox_usize(v_x_507_);
lean_dec(v_x_507_);
v_res_510_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_505_, v_x_1890__boxed_508_, v_x_1891__boxed_509_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(lean_object* v_x_511_, size_t v_x_512_){
_start:
{
uint64_t v___x_513_; size_t v___x_514_; lean_object* v___x_515_; 
v___x_513_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_512_);
v___x_514_ = lean_uint64_to_usize(v___x_513_);
v___x_515_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_511_, v___x_514_, v_x_512_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg___boxed(lean_object* v_x_516_, lean_object* v_x_517_){
_start:
{
size_t v_x_1953__boxed_518_; lean_object* v_res_519_; 
v_x_1953__boxed_518_ = lean_unbox_usize(v_x_517_);
lean_dec(v_x_517_);
v_res_519_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(v_x_516_, v_x_1953__boxed_518_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(lean_object* v_xs_520_, size_t v_v_521_, lean_object* v_i_522_){
_start:
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = lean_array_get_size(v_xs_520_);
v___x_524_ = lean_nat_dec_lt(v_i_522_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
lean_dec(v_i_522_);
v___x_525_ = lean_box(0);
return v___x_525_;
}
else
{
lean_object* v___x_526_; size_t v___x_527_; uint8_t v___x_528_; 
v___x_526_ = lean_array_fget_borrowed(v_xs_520_, v_i_522_);
v___x_527_ = lean_unbox_usize(v___x_526_);
v___x_528_ = lean_usize_dec_eq(v___x_527_, v_v_521_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(1u);
v___x_530_ = lean_nat_add(v_i_522_, v___x_529_);
lean_dec(v_i_522_);
v_i_522_ = v___x_530_;
goto _start;
}
else
{
lean_object* v___x_532_; 
v___x_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_532_, 0, v_i_522_);
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14___boxed(lean_object* v_xs_533_, lean_object* v_v_534_, lean_object* v_i_535_){
_start:
{
size_t v_v_boxed_536_; lean_object* v_res_537_; 
v_v_boxed_536_ = lean_unbox_usize(v_v_534_);
lean_dec(v_v_534_);
v_res_537_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(v_xs_533_, v_v_boxed_536_, v_i_535_);
lean_dec_ref(v_xs_533_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(lean_object* v_xs_538_, size_t v_v_539_){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(v_xs_538_, v_v_539_, v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11___boxed(lean_object* v_xs_542_, lean_object* v_v_543_){
_start:
{
size_t v_v_boxed_544_; lean_object* v_res_545_; 
v_v_boxed_544_ = lean_unbox_usize(v_v_543_);
lean_dec(v_v_543_);
v_res_545_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(v_xs_542_, v_v_boxed_544_);
lean_dec_ref(v_xs_542_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(lean_object* v_x_546_, size_t v_x_547_, size_t v_x_548_){
_start:
{
if (lean_obj_tag(v_x_546_) == 0)
{
lean_object* v_es_549_; lean_object* v___x_550_; size_t v___x_551_; size_t v___x_552_; size_t v___x_553_; lean_object* v_j_554_; lean_object* v_entry_555_; 
v_es_549_ = lean_ctor_get(v_x_546_, 0);
v___x_550_ = lean_box(2);
v___x_551_ = ((size_t)5ULL);
v___x_552_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1);
v___x_553_ = lean_usize_land(v_x_547_, v___x_552_);
v_j_554_ = lean_usize_to_nat(v___x_553_);
v_entry_555_ = lean_array_get(v___x_550_, v_es_549_, v_j_554_);
switch(lean_obj_tag(v_entry_555_))
{
case 0:
{
lean_object* v_key_556_; size_t v___x_557_; uint8_t v___x_558_; 
v_key_556_ = lean_ctor_get(v_entry_555_, 0);
lean_inc(v_key_556_);
lean_dec_ref(v_entry_555_);
v___x_557_ = lean_unbox_usize(v_key_556_);
lean_dec(v_key_556_);
v___x_558_ = lean_usize_dec_eq(v_x_548_, v___x_557_);
if (v___x_558_ == 0)
{
lean_dec(v_j_554_);
return v_x_546_;
}
else
{
lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_566_; 
lean_inc_ref(v_es_549_);
v_isSharedCheck_566_ = !lean_is_exclusive(v_x_546_);
if (v_isSharedCheck_566_ == 0)
{
lean_object* v_unused_567_; 
v_unused_567_ = lean_ctor_get(v_x_546_, 0);
lean_dec(v_unused_567_);
v___x_560_ = v_x_546_;
v_isShared_561_ = v_isSharedCheck_566_;
goto v_resetjp_559_;
}
else
{
lean_dec(v_x_546_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_566_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_562_ = lean_array_set(v_es_549_, v_j_554_, v___x_550_);
lean_dec(v_j_554_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v___x_562_);
v___x_564_ = v___x_560_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
case 1:
{
lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_601_; 
lean_inc_ref(v_es_549_);
v_isSharedCheck_601_ = !lean_is_exclusive(v_x_546_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v_x_546_, 0);
lean_dec(v_unused_602_);
v___x_569_ = v_x_546_;
v_isShared_570_ = v_isSharedCheck_601_;
goto v_resetjp_568_;
}
else
{
lean_dec(v_x_546_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_601_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v_node_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_600_; 
v_node_571_ = lean_ctor_get(v_entry_555_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v_entry_555_);
if (v_isSharedCheck_600_ == 0)
{
v___x_573_ = v_entry_555_;
v_isShared_574_ = v_isSharedCheck_600_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_node_571_);
lean_dec(v_entry_555_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_600_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v_entries_575_; size_t v___x_576_; lean_object* v_newNode_577_; lean_object* v___x_578_; 
v_entries_575_ = lean_array_set(v_es_549_, v_j_554_, v___x_550_);
v___x_576_ = lean_usize_shift_right(v_x_547_, v___x_551_);
v_newNode_577_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_node_571_, v___x_576_, v_x_548_);
lean_inc_ref(v_newNode_577_);
v___x_578_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_577_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v___x_580_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v_newNode_577_);
v___x_580_ = v___x_573_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_newNode_577_);
v___x_580_ = v_reuseFailAlloc_585_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_581_ = lean_array_set(v_entries_575_, v_j_554_, v___x_580_);
lean_dec(v_j_554_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_581_);
v___x_583_ = v___x_569_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
else
{
lean_object* v_val_586_; lean_object* v_fst_587_; lean_object* v_snd_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_599_; 
lean_dec_ref(v_newNode_577_);
lean_del_object(v___x_573_);
v_val_586_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_val_586_);
lean_dec_ref(v___x_578_);
v_fst_587_ = lean_ctor_get(v_val_586_, 0);
v_snd_588_ = lean_ctor_get(v_val_586_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v_val_586_);
if (v_isSharedCheck_599_ == 0)
{
v___x_590_ = v_val_586_;
v_isShared_591_ = v_isSharedCheck_599_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_snd_588_);
lean_inc(v_fst_587_);
lean_dec(v_val_586_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_599_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_fst_587_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_snd_588_);
v___x_593_ = v_reuseFailAlloc_598_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_594_ = lean_array_set(v_entries_575_, v_j_554_, v___x_593_);
lean_dec(v_j_554_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_594_);
v___x_596_ = v___x_569_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_554_);
return v_x_546_;
}
}
}
else
{
lean_object* v_ks_603_; lean_object* v_vs_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_618_; 
v_ks_603_ = lean_ctor_get(v_x_546_, 0);
v_vs_604_ = lean_ctor_get(v_x_546_, 1);
v_isSharedCheck_618_ = !lean_is_exclusive(v_x_546_);
if (v_isSharedCheck_618_ == 0)
{
v___x_606_ = v_x_546_;
v_isShared_607_ = v_isSharedCheck_618_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_vs_604_);
lean_inc(v_ks_603_);
lean_dec(v_x_546_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_618_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; 
v___x_608_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(v_ks_603_, v_x_548_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v___x_610_; 
if (v_isShared_607_ == 0)
{
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_ks_603_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_vs_604_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
else
{
lean_object* v_val_612_; lean_object* v_keys_x27_613_; lean_object* v_vals_x27_614_; lean_object* v___x_616_; 
v_val_612_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_val_612_);
lean_dec_ref(v___x_608_);
lean_inc(v_val_612_);
v_keys_x27_613_ = l_Array_eraseIdx___redArg(v_ks_603_, v_val_612_);
v_vals_x27_614_ = l_Array_eraseIdx___redArg(v_vs_604_, v_val_612_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v_vals_x27_614_);
lean_ctor_set(v___x_606_, 0, v_keys_x27_613_);
v___x_616_ = v___x_606_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_keys_x27_613_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_vals_x27_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg___boxed(lean_object* v_x_619_, lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
size_t v_x_1995__boxed_622_; size_t v_x_1996__boxed_623_; lean_object* v_res_624_; 
v_x_1995__boxed_622_ = lean_unbox_usize(v_x_620_);
lean_dec(v_x_620_);
v_x_1996__boxed_623_ = lean_unbox_usize(v_x_621_);
lean_dec(v_x_621_);
v_res_624_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_619_, v_x_1995__boxed_622_, v_x_1996__boxed_623_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(lean_object* v_x_625_, size_t v_x_626_){
_start:
{
uint64_t v___x_627_; size_t v_h_628_; lean_object* v___x_629_; 
v___x_627_ = lean_usize_to_uint64(v_x_626_);
v_h_628_ = lean_uint64_to_usize(v___x_627_);
v___x_629_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_625_, v_h_628_, v_x_626_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg___boxed(lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
size_t v_x_2135__boxed_632_; lean_object* v_res_633_; 
v_x_2135__boxed_632_ = lean_unbox_usize(v_x_631_);
lean_dec(v_x_631_);
v_res_633_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(v_x_630_, v_x_2135__boxed_632_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_x_634_, lean_object* v_x_635_, size_t v_x_636_, lean_object* v_x_637_){
_start:
{
lean_object* v_ks_638_; lean_object* v_vs_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_666_; 
v_ks_638_ = lean_ctor_get(v_x_634_, 0);
v_vs_639_ = lean_ctor_get(v_x_634_, 1);
v_isSharedCheck_666_ = !lean_is_exclusive(v_x_634_);
if (v_isSharedCheck_666_ == 0)
{
v___x_641_ = v_x_634_;
v_isShared_642_ = v_isSharedCheck_666_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_vs_639_);
lean_inc(v_ks_638_);
lean_dec(v_x_634_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_666_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_643_ = lean_array_get_size(v_ks_638_);
v___x_644_ = lean_nat_dec_lt(v_x_635_, v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
lean_dec(v_x_635_);
v___x_645_ = lean_box_usize(v_x_636_);
v___x_646_ = lean_array_push(v_ks_638_, v___x_645_);
v___x_647_ = lean_array_push(v_vs_639_, v_x_637_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v___x_647_);
lean_ctor_set(v___x_641_, 0, v___x_646_);
v___x_649_ = v___x_641_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
else
{
lean_object* v_k_x27_651_; size_t v___x_652_; uint8_t v___x_653_; 
v_k_x27_651_ = lean_array_fget_borrowed(v_ks_638_, v_x_635_);
v___x_652_ = lean_unbox_usize(v_k_x27_651_);
v___x_653_ = lean_usize_dec_eq(v_x_636_, v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_655_; 
if (v_isShared_642_ == 0)
{
v___x_655_ = v___x_641_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_ks_638_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_vs_639_);
v___x_655_ = v_reuseFailAlloc_659_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = lean_nat_add(v_x_635_, v___x_656_);
lean_dec(v_x_635_);
v_x_634_ = v___x_655_;
v_x_635_ = v___x_657_;
goto _start;
}
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_660_ = lean_box_usize(v_x_636_);
v___x_661_ = lean_array_fset(v_ks_638_, v_x_635_, v___x_660_);
v___x_662_ = lean_array_fset(v_vs_639_, v_x_635_, v_x_637_);
lean_dec(v_x_635_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v___x_662_);
lean_ctor_set(v___x_641_, 0, v___x_661_);
v___x_664_ = v___x_641_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_x_667_, lean_object* v_x_668_, lean_object* v_x_669_, lean_object* v_x_670_){
_start:
{
size_t v_x_2146__boxed_671_; lean_object* v_res_672_; 
v_x_2146__boxed_671_ = lean_unbox_usize(v_x_669_);
lean_dec(v_x_669_);
v_res_672_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_x_667_, v_x_668_, v_x_2146__boxed_671_, v_x_670_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(lean_object* v_n_673_, size_t v_k_674_, lean_object* v_v_675_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_n_673_, v___x_676_, v_k_674_, v_v_675_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_n_678_, lean_object* v_k_679_, lean_object* v_v_680_){
_start:
{
size_t v_k_boxed_681_; lean_object* v_res_682_; 
v_k_boxed_681_ = lean_unbox_usize(v_k_679_);
lean_dec(v_k_679_);
v_res_682_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v_n_678_, v_k_boxed_681_, v_v_680_);
return v_res_682_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(lean_object* v_x_684_, size_t v_x_685_, size_t v_x_686_, size_t v_x_687_, lean_object* v_x_688_){
_start:
{
if (lean_obj_tag(v_x_684_) == 0)
{
lean_object* v_es_689_; size_t v___x_690_; size_t v___x_691_; size_t v___x_692_; size_t v___x_693_; lean_object* v_j_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v_es_689_ = lean_ctor_get(v_x_684_, 0);
v___x_690_ = ((size_t)5ULL);
v___x_691_ = ((size_t)1ULL);
v___x_692_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1);
v___x_693_ = lean_usize_land(v_x_685_, v___x_692_);
v_j_694_ = lean_usize_to_nat(v___x_693_);
v___x_695_ = lean_array_get_size(v_es_689_);
v___x_696_ = lean_nat_dec_lt(v_j_694_, v___x_695_);
if (v___x_696_ == 0)
{
lean_dec(v_j_694_);
lean_dec(v_x_688_);
return v_x_684_;
}
else
{
lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_737_; 
lean_inc_ref(v_es_689_);
v_isSharedCheck_737_ = !lean_is_exclusive(v_x_684_);
if (v_isSharedCheck_737_ == 0)
{
lean_object* v_unused_738_; 
v_unused_738_ = lean_ctor_get(v_x_684_, 0);
lean_dec(v_unused_738_);
v___x_698_ = v_x_684_;
v_isShared_699_ = v_isSharedCheck_737_;
goto v_resetjp_697_;
}
else
{
lean_dec(v_x_684_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_737_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_v_700_; lean_object* v___x_701_; lean_object* v_xs_x27_702_; lean_object* v___y_704_; 
v_v_700_ = lean_array_fget(v_es_689_, v_j_694_);
v___x_701_ = lean_box(0);
v_xs_x27_702_ = lean_array_fset(v_es_689_, v_j_694_, v___x_701_);
switch(lean_obj_tag(v_v_700_))
{
case 0:
{
lean_object* v_key_709_; lean_object* v_val_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_723_; 
v_key_709_ = lean_ctor_get(v_v_700_, 0);
v_val_710_ = lean_ctor_get(v_v_700_, 1);
v_isSharedCheck_723_ = !lean_is_exclusive(v_v_700_);
if (v_isSharedCheck_723_ == 0)
{
v___x_712_ = v_v_700_;
v_isShared_713_ = v_isSharedCheck_723_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_val_710_);
lean_inc(v_key_709_);
lean_dec(v_v_700_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_723_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
size_t v___x_714_; uint8_t v___x_715_; 
v___x_714_ = lean_unbox_usize(v_key_709_);
v___x_715_ = lean_usize_dec_eq(v_x_687_, v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
lean_del_object(v___x_712_);
v___x_716_ = lean_box_usize(v_x_687_);
v___x_717_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_709_, v_val_710_, v___x_716_, v_x_688_);
v___x_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
v___y_704_ = v___x_718_;
goto v___jp_703_;
}
else
{
lean_object* v___x_719_; lean_object* v___x_721_; 
lean_dec(v_val_710_);
lean_dec(v_key_709_);
v___x_719_ = lean_box_usize(v_x_687_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 1, v_x_688_);
lean_ctor_set(v___x_712_, 0, v___x_719_);
v___x_721_ = v___x_712_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_x_688_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
v___y_704_ = v___x_721_;
goto v___jp_703_;
}
}
}
}
case 1:
{
lean_object* v_node_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_734_; 
v_node_724_ = lean_ctor_get(v_v_700_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v_v_700_);
if (v_isSharedCheck_734_ == 0)
{
v___x_726_ = v_v_700_;
v_isShared_727_ = v_isSharedCheck_734_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_node_724_);
lean_dec(v_v_700_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_734_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
size_t v___x_728_; size_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_728_ = lean_usize_shift_right(v_x_685_, v___x_690_);
v___x_729_ = lean_usize_add(v_x_686_, v___x_691_);
v___x_730_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_node_724_, v___x_728_, v___x_729_, v_x_687_, v_x_688_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_730_);
v___x_732_ = v___x_726_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
v___y_704_ = v___x_732_;
goto v___jp_703_;
}
}
}
default: 
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_box_usize(v_x_687_);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_ctor_set(v___x_736_, 1, v_x_688_);
v___y_704_ = v___x_736_;
goto v___jp_703_;
}
}
v___jp_703_:
{
lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_705_ = lean_array_fset(v_xs_x27_702_, v_j_694_, v___y_704_);
lean_dec(v_j_694_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_705_);
v___x_707_ = v___x_698_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
else
{
lean_object* v_ks_739_; lean_object* v_vs_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_760_; 
v_ks_739_ = lean_ctor_get(v_x_684_, 0);
v_vs_740_ = lean_ctor_get(v_x_684_, 1);
v_isSharedCheck_760_ = !lean_is_exclusive(v_x_684_);
if (v_isSharedCheck_760_ == 0)
{
v___x_742_ = v_x_684_;
v_isShared_743_ = v_isSharedCheck_760_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_vs_740_);
lean_inc(v_ks_739_);
lean_dec(v_x_684_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_760_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_ks_739_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_vs_740_);
v___x_745_ = v_reuseFailAlloc_759_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_object* v_newNode_746_; uint8_t v___y_748_; size_t v___x_754_; uint8_t v___x_755_; 
v_newNode_746_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v___x_745_, v_x_687_, v_x_688_);
v___x_754_ = ((size_t)7ULL);
v___x_755_ = lean_usize_dec_le(v___x_754_, v_x_686_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_756_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_746_);
v___x_757_ = lean_unsigned_to_nat(4u);
v___x_758_ = lean_nat_dec_lt(v___x_756_, v___x_757_);
lean_dec(v___x_756_);
v___y_748_ = v___x_758_;
goto v___jp_747_;
}
else
{
v___y_748_ = v___x_755_;
goto v___jp_747_;
}
v___jp_747_:
{
if (v___y_748_ == 0)
{
lean_object* v_ks_749_; lean_object* v_vs_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_ks_749_ = lean_ctor_get(v_newNode_746_, 0);
lean_inc_ref(v_ks_749_);
v_vs_750_ = lean_ctor_get(v_newNode_746_, 1);
lean_inc_ref(v_vs_750_);
lean_dec_ref(v_newNode_746_);
v___x_751_ = lean_unsigned_to_nat(0u);
v___x_752_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0);
v___x_753_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_x_686_, v_ks_749_, v_vs_750_, v___x_751_, v___x_752_);
lean_dec_ref(v_vs_750_);
lean_dec_ref(v_ks_749_);
return v___x_753_;
}
else
{
return v_newNode_746_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(size_t v_depth_761_, lean_object* v_keys_762_, lean_object* v_vals_763_, lean_object* v_i_764_, lean_object* v_entries_765_){
_start:
{
lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_766_ = lean_array_get_size(v_keys_762_);
v___x_767_ = lean_nat_dec_lt(v_i_764_, v___x_766_);
if (v___x_767_ == 0)
{
lean_dec(v_i_764_);
return v_entries_765_;
}
else
{
lean_object* v_k_768_; lean_object* v_v_769_; size_t v___x_770_; uint64_t v___x_771_; size_t v_h_772_; size_t v___x_773_; lean_object* v___x_774_; size_t v___x_775_; size_t v___x_776_; size_t v___x_777_; size_t v_h_778_; lean_object* v___x_779_; size_t v___x_780_; lean_object* v___x_781_; 
v_k_768_ = lean_array_fget_borrowed(v_keys_762_, v_i_764_);
v_v_769_ = lean_array_fget_borrowed(v_vals_763_, v_i_764_);
v___x_770_ = lean_unbox_usize(v_k_768_);
v___x_771_ = l_Lean_Lsp_instHashableRpcRef_hash(v___x_770_);
v_h_772_ = lean_uint64_to_usize(v___x_771_);
v___x_773_ = ((size_t)5ULL);
v___x_774_ = lean_unsigned_to_nat(1u);
v___x_775_ = ((size_t)1ULL);
v___x_776_ = lean_usize_sub(v_depth_761_, v___x_775_);
v___x_777_ = lean_usize_mul(v___x_773_, v___x_776_);
v_h_778_ = lean_usize_shift_right(v_h_772_, v___x_777_);
v___x_779_ = lean_nat_add(v_i_764_, v___x_774_);
lean_dec(v_i_764_);
v___x_780_ = lean_unbox_usize(v_k_768_);
lean_inc(v_v_769_);
v___x_781_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_entries_765_, v_h_778_, v_depth_761_, v___x_780_, v_v_769_);
v_i_764_ = v___x_779_;
v_entries_765_ = v___x_781_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_783_, lean_object* v_keys_784_, lean_object* v_vals_785_, lean_object* v_i_786_, lean_object* v_entries_787_){
_start:
{
size_t v_depth_boxed_788_; lean_object* v_res_789_; 
v_depth_boxed_788_ = lean_unbox_usize(v_depth_783_);
lean_dec(v_depth_783_);
v_res_789_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_depth_boxed_788_, v_keys_784_, v_vals_785_, v_i_786_, v_entries_787_);
lean_dec_ref(v_vals_785_);
lean_dec_ref(v_keys_784_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___boxed(lean_object* v_x_790_, lean_object* v_x_791_, lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
size_t v_x_2237__boxed_795_; size_t v_x_2238__boxed_796_; size_t v_x_2239__boxed_797_; lean_object* v_res_798_; 
v_x_2237__boxed_795_ = lean_unbox_usize(v_x_791_);
lean_dec(v_x_791_);
v_x_2238__boxed_796_ = lean_unbox_usize(v_x_792_);
lean_dec(v_x_792_);
v_x_2239__boxed_797_ = lean_unbox_usize(v_x_793_);
lean_dec(v_x_793_);
v_res_798_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_790_, v_x_2237__boxed_795_, v_x_2238__boxed_796_, v_x_2239__boxed_797_, v_x_794_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(lean_object* v_x_799_, size_t v_x_800_, lean_object* v_x_801_){
_start:
{
uint64_t v___x_802_; size_t v___x_803_; size_t v___x_804_; lean_object* v___x_805_; 
v___x_802_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_800_);
v___x_803_ = lean_uint64_to_usize(v___x_802_);
v___x_804_ = ((size_t)1ULL);
v___x_805_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_799_, v___x_803_, v___x_804_, v_x_800_, v_x_801_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg___boxed(lean_object* v_x_806_, lean_object* v_x_807_, lean_object* v_x_808_){
_start:
{
size_t v_x_2405__boxed_809_; lean_object* v_res_810_; 
v_x_2405__boxed_809_ = lean_unbox_usize(v_x_807_);
lean_dec(v_x_807_);
v_res_810_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(v_x_806_, v_x_2405__boxed_809_, v_x_808_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcReleaseRef(size_t v_r_811_, lean_object* v_a_812_){
_start:
{
lean_object* v___y_814_; lean_object* v_aliveRefs_818_; lean_object* v_refsById_819_; size_t v_nextRef_820_; lean_object* v___x_821_; 
v_aliveRefs_818_ = lean_ctor_get(v_a_812_, 0);
v_refsById_819_ = lean_ctor_get(v_a_812_, 1);
v_nextRef_820_ = lean_ctor_get_usize(v_a_812_, 2);
lean_inc_ref(v_aliveRefs_818_);
v___x_821_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(v_aliveRefs_818_, v_r_811_);
if (lean_obj_tag(v___x_821_) == 1)
{
lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_849_; 
lean_inc_ref(v_refsById_819_);
lean_inc_ref(v_aliveRefs_818_);
v_isSharedCheck_849_ = !lean_is_exclusive(v_a_812_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; lean_object* v_unused_851_; 
v_unused_850_ = lean_ctor_get(v_a_812_, 1);
lean_dec(v_unused_850_);
v_unused_851_ = lean_ctor_get(v_a_812_, 0);
lean_dec(v_unused_851_);
v___x_823_ = v_a_812_;
v_isShared_824_ = v_isSharedCheck_849_;
goto v_resetjp_822_;
}
else
{
lean_dec(v_a_812_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_849_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v_val_825_; lean_object* v_obj_826_; size_t v_id_827_; lean_object* v_rc_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_848_; 
v_val_825_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_val_825_);
lean_dec_ref(v___x_821_);
v_obj_826_ = lean_ctor_get(v_val_825_, 0);
v_id_827_ = lean_ctor_get_usize(v_val_825_, 2);
v_rc_828_ = lean_ctor_get(v_val_825_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v_val_825_);
if (v_isSharedCheck_848_ == 0)
{
v___x_830_ = v_val_825_;
v_isShared_831_ = v_isSharedCheck_848_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_rc_828_);
lean_inc(v_obj_826_);
lean_dec(v_val_825_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_848_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_832_ = lean_unsigned_to_nat(1u);
v___x_833_ = lean_nat_sub(v_rc_828_, v___x_832_);
lean_dec(v_rc_828_);
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = lean_nat_dec_eq(v___x_833_, v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_837_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 1, v___x_833_);
v___x_837_ = v___x_830_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_obj_826_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v___x_833_);
lean_ctor_set_usize(v_reuseFailAlloc_842_, 2, v_id_827_);
v___x_837_ = v_reuseFailAlloc_842_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_838_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(v_aliveRefs_818_, v_r_811_, v___x_837_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_838_);
v___x_840_ = v___x_823_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_refsById_819_);
lean_ctor_set_usize(v_reuseFailAlloc_841_, 2, v_nextRef_820_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
v___y_814_ = v___x_840_;
goto v___jp_813_;
}
}
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
lean_dec(v___x_833_);
lean_del_object(v___x_830_);
lean_dec(v_obj_826_);
v___x_843_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(v_aliveRefs_818_, v_r_811_);
v___x_844_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(v_refsById_819_, v_id_827_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v___x_844_);
lean_ctor_set(v___x_823_, 0, v___x_843_);
v___x_846_ = v___x_823_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_844_);
lean_ctor_set_usize(v_reuseFailAlloc_847_, 2, v_nextRef_820_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
v___y_814_ = v___x_846_;
goto v___jp_813_;
}
}
}
}
}
else
{
uint8_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
lean_dec(v___x_821_);
v___x_852_ = 0;
v___x_853_ = lean_box(v___x_852_);
v___x_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
lean_ctor_set(v___x_854_, 1, v_a_812_);
return v___x_854_;
}
v___jp_813_:
{
uint8_t v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = 1;
v___x_816_ = lean_box(v___x_815_);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v___y_814_);
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcReleaseRef___boxed(lean_object* v_r_855_, lean_object* v_a_856_){
_start:
{
size_t v_r_boxed_857_; lean_object* v_res_858_; 
v_r_boxed_857_ = lean_unbox_usize(v_r_855_);
lean_dec(v_r_855_);
v_res_858_ = l_Lean_Server_rpcReleaseRef(v_r_boxed_857_, v_a_856_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0(lean_object* v_00_u03b2_859_, lean_object* v_x_860_, size_t v_x_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(v_x_860_, v_x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___boxed(lean_object* v_00_u03b2_863_, lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
size_t v_x_2497__boxed_866_; lean_object* v_res_867_; 
v_x_2497__boxed_866_ = lean_unbox_usize(v_x_865_);
lean_dec(v_x_865_);
v_res_867_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0(v_00_u03b2_863_, v_x_864_, v_x_2497__boxed_866_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1(lean_object* v_00_u03b2_868_, lean_object* v_x_869_, size_t v_x_870_, lean_object* v_x_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(v_x_869_, v_x_870_, v_x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___boxed(lean_object* v_00_u03b2_873_, lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
size_t v_x_2505__boxed_877_; lean_object* v_res_878_; 
v_x_2505__boxed_877_ = lean_unbox_usize(v_x_875_);
lean_dec(v_x_875_);
v_res_878_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1(v_00_u03b2_873_, v_x_874_, v_x_2505__boxed_877_, v_x_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2(lean_object* v_00_u03b2_879_, lean_object* v_x_880_, size_t v_x_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(v_x_880_, v_x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___boxed(lean_object* v_00_u03b2_883_, lean_object* v_x_884_, lean_object* v_x_885_){
_start:
{
size_t v_x_2516__boxed_886_; lean_object* v_res_887_; 
v_x_2516__boxed_886_ = lean_unbox_usize(v_x_885_);
lean_dec(v_x_885_);
v_res_887_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2(v_00_u03b2_883_, v_x_884_, v_x_2516__boxed_886_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3(lean_object* v_00_u03b2_888_, lean_object* v_x_889_, size_t v_x_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(v_x_889_, v_x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___boxed(lean_object* v_00_u03b2_892_, lean_object* v_x_893_, lean_object* v_x_894_){
_start:
{
size_t v_x_2524__boxed_895_; lean_object* v_res_896_; 
v_x_2524__boxed_895_ = lean_unbox_usize(v_x_894_);
lean_dec(v_x_894_);
v_res_896_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3(v_00_u03b2_892_, v_x_893_, v_x_2524__boxed_895_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0(lean_object* v_00_u03b2_897_, lean_object* v_x_898_, size_t v_x_899_, size_t v_x_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_898_, v_x_899_, v_x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___boxed(lean_object* v_00_u03b2_902_, lean_object* v_x_903_, lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
size_t v_x_2532__boxed_906_; size_t v_x_2533__boxed_907_; lean_object* v_res_908_; 
v_x_2532__boxed_906_ = lean_unbox_usize(v_x_904_);
lean_dec(v_x_904_);
v_x_2533__boxed_907_ = lean_unbox_usize(v_x_905_);
lean_dec(v_x_905_);
v_res_908_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0(v_00_u03b2_902_, v_x_903_, v_x_2532__boxed_906_, v_x_2533__boxed_907_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2(lean_object* v_00_u03b2_909_, lean_object* v_x_910_, size_t v_x_911_, size_t v_x_912_, size_t v_x_913_, lean_object* v_x_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_910_, v_x_911_, v_x_912_, v_x_913_, v_x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___boxed(lean_object* v_00_u03b2_916_, lean_object* v_x_917_, lean_object* v_x_918_, lean_object* v_x_919_, lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
size_t v_x_2543__boxed_922_; size_t v_x_2544__boxed_923_; size_t v_x_2545__boxed_924_; lean_object* v_res_925_; 
v_x_2543__boxed_922_ = lean_unbox_usize(v_x_918_);
lean_dec(v_x_918_);
v_x_2544__boxed_923_ = lean_unbox_usize(v_x_919_);
lean_dec(v_x_919_);
v_x_2545__boxed_924_ = lean_unbox_usize(v_x_920_);
lean_dec(v_x_920_);
v_res_925_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2(v_00_u03b2_916_, v_x_917_, v_x_2543__boxed_922_, v_x_2544__boxed_923_, v_x_2545__boxed_924_, v_x_921_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4(lean_object* v_00_u03b2_926_, lean_object* v_x_927_, size_t v_x_928_, size_t v_x_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_x_927_, v_x_928_, v_x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___boxed(lean_object* v_00_u03b2_931_, lean_object* v_x_932_, lean_object* v_x_933_, lean_object* v_x_934_){
_start:
{
size_t v_x_2560__boxed_935_; size_t v_x_2561__boxed_936_; lean_object* v_res_937_; 
v_x_2560__boxed_935_ = lean_unbox_usize(v_x_933_);
lean_dec(v_x_933_);
v_x_2561__boxed_936_ = lean_unbox_usize(v_x_934_);
lean_dec(v_x_934_);
v_res_937_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4(v_00_u03b2_931_, v_x_932_, v_x_2560__boxed_935_, v_x_2561__boxed_936_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6(lean_object* v_00_u03b2_938_, lean_object* v_x_939_, size_t v_x_940_, size_t v_x_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_939_, v_x_940_, v_x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___boxed(lean_object* v_00_u03b2_943_, lean_object* v_x_944_, lean_object* v_x_945_, lean_object* v_x_946_){
_start:
{
size_t v_x_2571__boxed_947_; size_t v_x_2572__boxed_948_; lean_object* v_res_949_; 
v_x_2571__boxed_947_ = lean_unbox_usize(v_x_945_);
lean_dec(v_x_945_);
v_x_2572__boxed_948_ = lean_unbox_usize(v_x_946_);
lean_dec(v_x_946_);
v_res_949_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6(v_00_u03b2_943_, v_x_944_, v_x_2571__boxed_947_, v_x_2572__boxed_948_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_950_, lean_object* v_keys_951_, lean_object* v_vals_952_, lean_object* v_heq_953_, lean_object* v_i_954_, size_t v_k_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(v_keys_951_, v_vals_952_, v_i_954_, v_k_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_957_, lean_object* v_keys_958_, lean_object* v_vals_959_, lean_object* v_heq_960_, lean_object* v_i_961_, lean_object* v_k_962_){
_start:
{
size_t v_k_boxed_963_; lean_object* v_res_964_; 
v_k_boxed_963_ = lean_unbox_usize(v_k_962_);
lean_dec(v_k_962_);
v_res_964_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1(v_00_u03b2_957_, v_keys_958_, v_vals_959_, v_heq_960_, v_i_961_, v_k_boxed_963_);
lean_dec_ref(v_vals_959_);
lean_dec_ref(v_keys_958_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_965_, lean_object* v_n_966_, size_t v_k_967_, lean_object* v_v_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v_n_966_, v_k_967_, v_v_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_970_, lean_object* v_n_971_, lean_object* v_k_972_, lean_object* v_v_973_){
_start:
{
size_t v_k_boxed_974_; lean_object* v_res_975_; 
v_k_boxed_974_ = lean_unbox_usize(v_k_972_);
lean_dec(v_k_972_);
v_res_975_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4(v_00_u03b2_970_, v_n_971_, v_k_boxed_974_, v_v_973_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_976_, size_t v_depth_977_, lean_object* v_keys_978_, lean_object* v_vals_979_, lean_object* v_heq_980_, lean_object* v_i_981_, lean_object* v_entries_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_depth_977_, v_keys_978_, v_vals_979_, v_i_981_, v_entries_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_984_, lean_object* v_depth_985_, lean_object* v_keys_986_, lean_object* v_vals_987_, lean_object* v_heq_988_, lean_object* v_i_989_, lean_object* v_entries_990_){
_start:
{
size_t v_depth_boxed_991_; lean_object* v_res_992_; 
v_depth_boxed_991_ = lean_unbox_usize(v_depth_985_);
lean_dec(v_depth_985_);
v_res_992_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5(v_00_u03b2_984_, v_depth_boxed_991_, v_keys_986_, v_vals_987_, v_heq_988_, v_i_989_, v_entries_990_);
lean_dec_ref(v_vals_987_);
lean_dec_ref(v_keys_986_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_993_, lean_object* v_x_994_, lean_object* v_x_995_, size_t v_x_996_, lean_object* v_x_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_x_994_, v_x_995_, v_x_996_, v_x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_999_, lean_object* v_x_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_){
_start:
{
size_t v_x_2589__boxed_1004_; lean_object* v_res_1005_; 
v_x_2589__boxed_1004_ = lean_unbox_usize(v_x_1002_);
lean_dec(v_x_1002_);
v_res_1005_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7(v_00_u03b2_999_, v_x_1000_, v_x_1001_, v_x_2589__boxed_1004_, v_x_1003_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__0(lean_object* v_inst_1006_, lean_object* v_a_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = lean_apply_1(v_inst_1006_, v_a_1007_);
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set(v___x_1010_, 1, v___y_1008_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1(lean_object* v_inst_1011_, lean_object* v___x_1012_, lean_object* v___x_1013_, lean_object* v_j_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_201__overap_1017_; lean_object* v___x_1018_; 
v___x_1016_ = lean_apply_1(v_inst_1011_, v_j_1014_);
v___x_201__overap_1017_ = l_MonadExcept_ofExcept___redArg(v___x_1012_, v___x_1013_, v___x_1016_);
v___x_1018_ = lean_apply_1(v___x_201__overap_1017_, v___y_1015_);
return v___x_1018_;
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
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v_toApplicative_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1086_; 
v___x_1070_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1071_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20);
v_toApplicative_1072_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1086_ == 0)
{
lean_object* v_unused_1087_; 
v_unused_1087_ = lean_ctor_get(v___x_1070_, 1);
lean_dec(v_unused_1087_);
v___x_1074_ = v___x_1070_;
v_isShared_1075_ = v_isSharedCheck_1086_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_toApplicative_1072_);
lean_dec(v___x_1070_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1086_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v_toPure_1076_; lean_object* v___f_1077_; lean_object* v___f_1078_; lean_object* v___x_1079_; lean_object* v___x_1081_; 
v_toPure_1076_ = lean_ctor_get(v_toApplicative_1072_, 1);
lean_inc(v_toPure_1076_);
lean_dec_ref(v_toApplicative_1072_);
v___f_1077_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1077_, 0, v_inst_1069_);
v___f_1078_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptTOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1078_, 0, v_toPure_1076_);
v___x_1079_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 1, v___x_1079_);
lean_ctor_set(v___x_1074_, 0, v___f_1078_);
v___x_1081_ = v___x_1074_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___f_1078_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1082_; lean_object* v___f_1083_; lean_object* v___x_1084_; 
v___x_1082_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_1081_);
v___f_1083_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1083_, 0, v_inst_1068_);
lean_closure_set(v___f_1083_, 1, v___x_1071_);
lean_closure_set(v___f_1083_, 2, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___f_1077_);
lean_ctor_set(v___x_1084_, 1, v___f_1083_);
return v___x_1084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson(lean_object* v_00_u03b1_1088_, lean_object* v_inst_1089_, lean_object* v_inst_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg(v_inst_1089_, v_inst_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg___lam__0(lean_object* v_inst_1092_, lean_object* v___x_1093_, lean_object* v_v_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_fst_1097_; lean_object* v_snd_1098_; 
if (lean_obj_tag(v_v_1094_) == 0)
{
lean_object* v___x_1101_; 
lean_dec_ref(v_inst_1092_);
v___x_1101_ = lean_box(0);
v_fst_1097_ = v___x_1101_;
v_snd_1098_ = v___y_1095_;
goto v___jp_1096_;
}
else
{
lean_object* v_rpcEncode_1102_; lean_object* v_val_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1113_; 
v_rpcEncode_1102_ = lean_ctor_get(v_inst_1092_, 0);
lean_inc_ref(v_rpcEncode_1102_);
lean_dec_ref(v_inst_1092_);
v_val_1103_ = lean_ctor_get(v_v_1094_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_v_1094_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1105_ = v_v_1094_;
v_isShared_1106_ = v_isSharedCheck_1113_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_val_1103_);
lean_dec(v_v_1094_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1113_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; lean_object* v_fst_1108_; lean_object* v_snd_1109_; lean_object* v___x_1111_; 
v___x_1107_ = lean_apply_2(v_rpcEncode_1102_, v_val_1103_, v___y_1095_);
v_fst_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_fst_1108_);
v_snd_1109_ = lean_ctor_get(v___x_1107_, 1);
lean_inc(v_snd_1109_);
lean_dec_ref(v___x_1107_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v_fst_1108_);
v___x_1111_ = v___x_1105_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_fst_1108_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
v_fst_1097_ = v___x_1111_;
v_snd_1098_ = v_snd_1109_;
goto v___jp_1096_;
}
}
}
v___jp_1096_:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = l_Option_toJson___redArg(v___x_1093_, v_fst_1097_);
v___x_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
lean_ctor_set(v___x_1100_, 1, v_snd_1098_);
return v___x_1100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg___lam__1(lean_object* v___f_1116_, lean_object* v_inst_1117_, lean_object* v_j_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_Option_fromJson_x3f___redArg(v___f_1116_, v_j_1118_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec_ref(v___y_1119_);
lean_dec_ref(v_inst_1117_);
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1120_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1120_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
else
{
lean_object* v_a_1129_; 
v_a_1129_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1129_);
lean_dec_ref(v___x_1120_);
if (lean_obj_tag(v_a_1129_) == 0)
{
lean_object* v___x_1130_; 
lean_dec_ref(v___y_1119_);
lean_dec_ref(v_inst_1117_);
v___x_1130_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___lam__1___closed__0));
return v___x_1130_;
}
else
{
lean_object* v_rpcDecode_1131_; lean_object* v_val_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1156_; 
v_rpcDecode_1131_ = lean_ctor_get(v_inst_1117_, 1);
lean_inc_ref(v_rpcDecode_1131_);
lean_dec_ref(v_inst_1117_);
v_val_1132_ = lean_ctor_get(v_a_1129_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_a_1129_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1134_ = v_a_1129_;
v_isShared_1135_ = v_isSharedCheck_1156_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_val_1132_);
lean_dec(v_a_1129_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1156_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_apply_2(v_rpcDecode_1131_, v_val_1132_, v___y_1119_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_del_object(v___x_1134_);
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1136_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1136_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1155_; 
v_a_1145_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1147_ = v___x_1136_;
v_isShared_1148_ = v_isSharedCheck_1155_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1136_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1155_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v_a_1145_);
v___x_1150_ = v___x_1134_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
lean_object* v___x_1152_; 
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1150_);
v___x_1152_ = v___x_1147_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg(lean_object* v_inst_1159_){
_start:
{
lean_object* v___x_1160_; lean_object* v___f_1161_; lean_object* v___f_1162_; lean_object* v___f_1163_; lean_object* v___x_1164_; 
v___x_1160_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__0));
lean_inc_ref(v_inst_1159_);
v___f_1161_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOption___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1161_, 0, v_inst_1159_);
lean_closure_set(v___f_1161_, 1, v___x_1160_);
v___f_1162_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__1));
v___f_1163_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOption___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1163_, 0, v___f_1162_);
lean_closure_set(v___f_1163_, 1, v_inst_1159_);
v___x_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___f_1161_);
lean_ctor_set(v___x_1164_, 1, v___f_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption(lean_object* v_00_u03b1_1165_, lean_object* v_inst_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Lean_Server_instRpcEncodableOption___redArg(v_inst_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__0(lean_object* v_inst_1168_, lean_object* v___x_1169_, lean_object* v___x_1170_, lean_object* v_a_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_rpcEncode_1173_; size_t v_sz_1174_; size_t v___x_1175_; lean_object* v___x_648__overap_1176_; lean_object* v___x_1177_; lean_object* v_fst_1178_; lean_object* v_snd_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1187_; 
v_rpcEncode_1173_ = lean_ctor_get(v_inst_1168_, 0);
lean_inc_ref(v_rpcEncode_1173_);
lean_dec_ref(v_inst_1168_);
v_sz_1174_ = lean_array_size(v_a_1171_);
v___x_1175_ = ((size_t)0ULL);
v___x_648__overap_1176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1169_, v_rpcEncode_1173_, v_sz_1174_, v___x_1175_, v_a_1171_);
v___x_1177_ = lean_apply_1(v___x_648__overap_1176_, v___y_1172_);
v_fst_1178_ = lean_ctor_get(v___x_1177_, 0);
v_snd_1179_ = lean_ctor_get(v___x_1177_, 1);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1181_ = v___x_1177_;
v_isShared_1182_ = v_isSharedCheck_1187_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_snd_1179_);
lean_inc(v_fst_1178_);
lean_dec(v___x_1177_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1187_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1183_ = l_Array_toJson___redArg(v___x_1170_, v_fst_1178_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1183_);
v___x_1185_ = v___x_1181_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_snd_1179_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__1(lean_object* v___f_1188_, lean_object* v_inst_1189_, lean_object* v___x_1190_, lean_object* v_b_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Array_fromJson_x3f___redArg(v___f_1188_, v_b_1191_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec_ref(v___y_1192_);
lean_dec_ref(v___x_1190_);
lean_dec_ref(v_inst_1189_);
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1193_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1193_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v_rpcDecode_1203_; size_t v_sz_1204_; size_t v___x_1205_; lean_object* v___x_662__overap_1206_; lean_object* v___x_1207_; 
v_a_1202_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1202_);
lean_dec_ref(v___x_1193_);
v_rpcDecode_1203_ = lean_ctor_get(v_inst_1189_, 1);
lean_inc_ref(v_rpcDecode_1203_);
lean_dec_ref(v_inst_1189_);
v_sz_1204_ = lean_array_size(v_a_1202_);
v___x_1205_ = ((size_t)0ULL);
v___x_662__overap_1206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1190_, v_rpcDecode_1203_, v_sz_1204_, v___x_1205_, v_a_1202_);
v___x_1207_ = lean_apply_1(v___x_662__overap_1206_, v___y_1192_);
return v___x_1207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg(lean_object* v_inst_1234_){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___f_1237_; lean_object* v___x_1238_; lean_object* v___f_1239_; lean_object* v___f_1240_; lean_object* v___x_1241_; 
v___x_1235_ = ((lean_object*)(l_Lean_Server_instRpcEncodableArray___redArg___closed__9));
v___x_1236_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__0));
lean_inc_ref(v_inst_1234_);
v___f_1237_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableArray___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1237_, 0, v_inst_1234_);
lean_closure_set(v___f_1237_, 1, v___x_1235_);
lean_closure_set(v___f_1237_, 2, v___x_1236_);
v___x_1238_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20);
v___f_1239_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__1));
v___f_1240_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableArray___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1240_, 0, v___f_1239_);
lean_closure_set(v___f_1240_, 1, v_inst_1234_);
lean_closure_set(v___f_1240_, 2, v___x_1238_);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___f_1237_);
lean_ctor_set(v___x_1241_, 1, v___f_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray(lean_object* v_00_u03b1_1242_, lean_object* v_inst_1243_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lean_Server_instRpcEncodableArray___redArg(v_inst_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg___lam__0(lean_object* v_inst_1245_, lean_object* v_inst_1246_, lean_object* v___x_1247_, lean_object* v_x_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_fst_1250_; lean_object* v_snd_1251_; lean_object* v_rpcEncode_1252_; lean_object* v___x_1253_; lean_object* v_fst_1254_; lean_object* v_snd_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1274_; 
v_fst_1250_ = lean_ctor_get(v_x_1248_, 0);
lean_inc(v_fst_1250_);
v_snd_1251_ = lean_ctor_get(v_x_1248_, 1);
lean_inc(v_snd_1251_);
lean_dec_ref(v_x_1248_);
v_rpcEncode_1252_ = lean_ctor_get(v_inst_1245_, 0);
lean_inc_ref(v_rpcEncode_1252_);
lean_dec_ref(v_inst_1245_);
v___x_1253_ = lean_apply_2(v_rpcEncode_1252_, v_fst_1250_, v___y_1249_);
v_fst_1254_ = lean_ctor_get(v___x_1253_, 0);
v_snd_1255_ = lean_ctor_get(v___x_1253_, 1);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1257_ = v___x_1253_;
v_isShared_1258_ = v_isSharedCheck_1274_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_snd_1255_);
lean_inc(v_fst_1254_);
lean_dec(v___x_1253_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1274_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v_rpcEncode_1259_; lean_object* v___x_1260_; lean_object* v_fst_1261_; lean_object* v_snd_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1273_; 
v_rpcEncode_1259_ = lean_ctor_get(v_inst_1246_, 0);
lean_inc_ref(v_rpcEncode_1259_);
lean_dec_ref(v_inst_1246_);
v___x_1260_ = lean_apply_2(v_rpcEncode_1259_, v_snd_1251_, v_snd_1255_);
v_fst_1261_ = lean_ctor_get(v___x_1260_, 0);
v_snd_1262_ = lean_ctor_get(v___x_1260_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1264_ = v___x_1260_;
v_isShared_1265_ = v_isSharedCheck_1273_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_snd_1262_);
lean_inc(v_fst_1261_);
lean_dec(v___x_1260_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1273_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 1, v_fst_1261_);
lean_ctor_set(v___x_1264_, 0, v_fst_1254_);
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_fst_1254_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_fst_1261_);
v___x_1267_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1268_; lean_object* v___x_1270_; 
lean_inc_ref(v___x_1247_);
v___x_1268_ = l_Prod_toJson___redArg(v___x_1247_, v___x_1247_, v___x_1267_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v_snd_1262_);
lean_ctor_set(v___x_1257_, 0, v___x_1268_);
v___x_1270_ = v___x_1257_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_snd_1262_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg___lam__1(lean_object* v___f_1275_, lean_object* v_inst_1276_, lean_object* v_inst_1277_, lean_object* v_j_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1280_; 
lean_inc_ref(v___f_1275_);
v___x_1280_ = l_Prod_fromJson_x3f___redArg(v___f_1275_, v___f_1275_, v_j_1278_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec_ref(v___y_1279_);
lean_dec_ref(v_inst_1277_);
lean_dec_ref(v_inst_1276_);
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v_fst_1290_; lean_object* v_snd_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1327_; 
v_a_1289_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1289_);
lean_dec_ref(v___x_1280_);
v_fst_1290_ = lean_ctor_get(v_a_1289_, 0);
v_snd_1291_ = lean_ctor_get(v_a_1289_, 1);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_a_1289_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1293_ = v_a_1289_;
v_isShared_1294_ = v_isSharedCheck_1327_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_snd_1291_);
lean_inc(v_fst_1290_);
lean_dec(v_a_1289_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1327_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v_rpcDecode_1295_; lean_object* v___x_1296_; 
v_rpcDecode_1295_ = lean_ctor_get(v_inst_1276_, 1);
lean_inc_ref(v_rpcDecode_1295_);
lean_dec_ref(v_inst_1276_);
lean_inc_ref(v___y_1279_);
v___x_1296_ = lean_apply_2(v_rpcDecode_1295_, v_fst_1290_, v___y_1279_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_del_object(v___x_1293_);
lean_dec(v_snd_1291_);
lean_dec_ref(v___y_1279_);
lean_dec_ref(v_inst_1277_);
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
lean_object* v_a_1305_; lean_object* v_rpcDecode_1306_; lean_object* v___x_1307_; 
v_a_1305_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1305_);
lean_dec_ref(v___x_1296_);
v_rpcDecode_1306_ = lean_ctor_get(v_inst_1277_, 1);
lean_inc_ref(v_rpcDecode_1306_);
lean_dec_ref(v_inst_1277_);
v___x_1307_ = lean_apply_2(v_rpcDecode_1306_, v_snd_1291_, v___y_1279_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_dec(v_a_1305_);
lean_del_object(v___x_1293_);
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
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1326_; 
v_a_1316_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1318_ = v___x_1307_;
v_isShared_1319_ = v_isSharedCheck_1326_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1307_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1326_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 1, v_a_1316_);
lean_ctor_set(v___x_1293_, 0, v_a_1305_);
v___x_1321_ = v___x_1293_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1305_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1323_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1321_);
v___x_1323_ = v___x_1318_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg(lean_object* v_inst_1328_, lean_object* v_inst_1329_){
_start:
{
lean_object* v___x_1330_; lean_object* v___f_1331_; lean_object* v___f_1332_; lean_object* v___f_1333_; lean_object* v___x_1334_; 
v___x_1330_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__0));
lean_inc_ref(v_inst_1329_);
lean_inc_ref(v_inst_1328_);
v___f_1331_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableProd___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1331_, 0, v_inst_1328_);
lean_closure_set(v___f_1331_, 1, v_inst_1329_);
lean_closure_set(v___f_1331_, 2, v___x_1330_);
v___f_1332_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__1));
v___f_1333_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableProd___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1333_, 0, v___f_1332_);
lean_closure_set(v___f_1333_, 1, v_inst_1328_);
lean_closure_set(v___f_1333_, 2, v_inst_1329_);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___f_1331_);
lean_ctor_set(v___x_1334_, 1, v___f_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd(lean_object* v_00_u03b1_1335_, lean_object* v_00_u03b2_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Lean_Server_instRpcEncodableProd___redArg(v_inst_1337_, v_inst_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__0(lean_object* v_inst_1340_, lean_object* v_fn_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_rpcEncode_1343_; lean_object* v___x_1344_; lean_object* v_fst_1345_; lean_object* v_snd_1346_; lean_object* v___x_1347_; 
v_rpcEncode_1343_ = lean_ctor_get(v_inst_1340_, 0);
lean_inc_ref(v_rpcEncode_1343_);
lean_dec_ref(v_inst_1340_);
v___x_1344_ = lean_apply_1(v_fn_1341_, v___y_1342_);
v_fst_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_fst_1345_);
v_snd_1346_ = lean_ctor_get(v___x_1344_, 1);
lean_inc(v_snd_1346_);
lean_dec_ref(v___x_1344_);
v___x_1347_ = lean_apply_2(v_rpcEncode_1343_, v_fst_1345_, v_snd_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1(lean_object* v_inst_1348_, lean_object* v___x_1349_, lean_object* v_j_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_rpcDecode_1352_; lean_object* v___x_1353_; 
v_rpcDecode_1352_ = lean_ctor_get(v_inst_1348_, 1);
lean_inc_ref(v_rpcDecode_1352_);
lean_dec_ref(v_inst_1348_);
v___x_1353_ = lean_apply_2(v_rpcDecode_1352_, v_j_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec_ref(v___x_1349_);
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1353_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1353_);
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
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1370_; 
v_a_1362_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1364_ = v___x_1353_;
v_isShared_1365_ = v_isSharedCheck_1370_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1353_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1370_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1366_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 5);
lean_closure_set(v___x_1366_, 0, lean_box(0));
lean_closure_set(v___x_1366_, 1, lean_box(0));
lean_closure_set(v___x_1366_, 2, v___x_1349_);
lean_closure_set(v___x_1366_, 3, lean_box(0));
lean_closure_set(v___x_1366_, 4, v_a_1362_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1366_);
v___x_1368_ = v___x_1364_;
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
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg(lean_object* v_inst_1371_){
_start:
{
lean_object* v___f_1372_; lean_object* v___x_1373_; lean_object* v___f_1374_; lean_object* v___x_1375_; 
lean_inc_ref(v_inst_1371_);
v___f_1372_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1372_, 0, v_inst_1371_);
v___x_1373_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9));
v___f_1374_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1374_, 0, v_inst_1371_);
lean_closure_set(v___f_1374_, 1, v___x_1373_);
v___x_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___f_1372_);
lean_ctor_set(v___x_1375_, 1, v___f_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore(lean_object* v_00_u03b1_1376_, lean_object* v_inst_1377_){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg(v_inst_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(lean_object* v_inst_1379_, lean_object* v_r_1380_, lean_object* v_a_1381_){
_start:
{
lean_object* v___x_1382_; lean_object* v_fst_1383_; lean_object* v_snd_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1393_; 
v___x_1382_ = l_Lean_Server_rpcStoreRef___redArg(v_inst_1379_, v_r_1380_, v_a_1381_);
v_fst_1383_ = lean_ctor_get(v___x_1382_, 0);
v_snd_1384_ = lean_ctor_get(v___x_1382_, 1);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1386_ = v___x_1382_;
v_isShared_1387_ = v_isSharedCheck_1393_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_snd_1384_);
lean_inc(v_fst_1383_);
lean_dec(v___x_1382_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1393_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
size_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1388_ = lean_unbox_usize(v_fst_1383_);
lean_dec(v_fst_1383_);
v___x_1389_ = l_Lean_Lsp_instToJsonRpcRef_toJson(v___x_1388_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1389_);
v___x_1391_ = v___x_1386_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_snd_1384_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg___boxed(lean_object* v_inst_1394_, lean_object* v_r_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(v_inst_1394_, v_r_1395_, v_a_1396_);
lean_dec_ref(v_r_1395_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode(lean_object* v_00_u03b1_1398_, lean_object* v_inst_1399_, lean_object* v_r_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(v_inst_1399_, v_r_1400_, v_a_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___boxed(lean_object* v_00_u03b1_1403_, lean_object* v_inst_1404_, lean_object* v_r_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode(v_00_u03b1_1403_, v_inst_1404_, v_r_1405_, v_a_1406_);
lean_dec_ref(v_r_1405_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(lean_object* v_inst_1408_, lean_object* v_j_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_Lsp_instFromJsonRpcRef_fromJson(v_j_1409_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_dec_ref(v_a_1410_);
lean_dec(v_inst_1408_);
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
lean_object* v_a_1420_; size_t v___x_1421_; lean_object* v___x_1422_; 
v_a_1420_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1420_);
lean_dec_ref(v___x_1411_);
v___x_1421_ = lean_unbox_usize(v_a_1420_);
lean_dec(v_a_1420_);
v___x_1422_ = l_Lean_Server_rpcGetRef___redArg(v_inst_1408_, v___x_1421_, v_a_1410_);
return v___x_1422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode(lean_object* v_00_u03b1_1423_, lean_object* v_inst_1424_, lean_object* v_j_1425_, lean_object* v_a_1426_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v_inst_1424_, v_j_1425_, v_a_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName___redArg(lean_object* v_inst_1428_){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_inc(v_inst_1428_);
v___x_1429_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___boxed), 4, 2);
lean_closure_set(v___x_1429_, 0, lean_box(0));
lean_closure_set(v___x_1429_, 1, v_inst_1428_);
v___x_1430_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode), 4, 2);
lean_closure_set(v___x_1430_, 0, lean_box(0));
lean_closure_set(v___x_1430_, 1, v_inst_1428_);
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1429_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName(lean_object* v_00_u03b1_1432_, lean_object* v_inst_1433_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName___redArg(v_inst_1433_);
return v___x_1434_;
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
res = l_Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_();
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
