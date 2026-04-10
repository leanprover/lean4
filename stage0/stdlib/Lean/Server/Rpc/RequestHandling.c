// Lean compiler output
// Module: Lean.Server.Rpc.RequestHandling
// Imports: public import Lean.Server.Requests
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
lean_object* l_Lean_Json_compress(lean_object*);
uint64_t lean_string_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_initializing();
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Prod_map___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson(lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
lean_object* l_Lean_Server_RequestM_asTask___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Server_instInhabitedRequestError_default;
extern lean_object* l_Lean_Server_requestHandlers;
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRpcProcedure_default___lam__0(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRpcProcedure_default___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_instInhabitedRpcProcedure_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_instInhabitedRpcProcedure_default___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instInhabitedRpcProcedure_default___closed__0 = (const lean_object*)&l_Lean_Server_instInhabitedRpcProcedure_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instInhabitedRpcProcedure_default = (const lean_object*)&l_Lean_Server_instInhabitedRpcProcedure_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instInhabitedRpcProcedure = (const lean_object*)&l_Lean_Server_instInhabitedRpcProcedure_default___closed__0_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Server"};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "userRpcProcedures"};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(32, 19, 140, 79, 36, 84, 215, 143)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_userRpcProcedures;
static const lean_string_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "RpcProcedure"};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__0 = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 154, 15, 100, 124, 232, 217, 30)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1 = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_existsBuiltinRpcProcedure(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_existsBuiltinRpcProcedure___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__0(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_handleRpcCall___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_handleRpcCall___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Failed to evaluate RPC constant '"};
static const lean_object* l_Lean_Server_handleRpcCall___lam__3___closed__0 = (const lean_object*)&l_Lean_Server_handleRpcCall___lam__3___closed__0_value;
static const lean_string_object l_Lean_Server_handleRpcCall___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "': "};
static const lean_object* l_Lean_Server_handleRpcCall___lam__3___closed__1 = (const lean_object*)&l_Lean_Server_handleRpcCall___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_handleRpcCall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "No RPC method '"};
static const lean_object* l_Lean_Server_handleRpcCall___closed__0 = (const lean_object*)&l_Lean_Server_handleRpcCall___closed__0_value;
static const lean_string_object l_Lean_Server_handleRpcCall___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "' found"};
static const lean_object* l_Lean_Server_handleRpcCall___closed__1 = (const lean_object*)&l_Lean_Server_handleRpcCall___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Cannot parse request params: "};
static const lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__0_value;
static const lean_string_object l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__0(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Failed to register LSP request handler for '"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__0_value;
static const lean_string_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "': only possible during initialization"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__1 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__1_value;
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__2 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__2_value;
static const lean_string_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "': already registered"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__3 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "$/lean/rpc/call"};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_handleRpcCall___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_wrapRpcProcedure___redArg___lam__0(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_wrapRpcProcedure___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Server_wrapRpcProcedure___redArg___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Cannot decode params in RPC call '"};
static const lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__0_value;
static const lean_string_object l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__1_value;
static const lean_string_object l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ")'\n"};
static const lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__2_value;
static const lean_string_object l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Outdated RPC session"};
static const lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__3_value;
static const lean_ctor_object l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(9, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_wrapRpcProcedure___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_wrapRpcProcedure___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_wrapRpcProcedure___redArg___closed__0 = (const lean_object*)&l_Lean_Server_wrapRpcProcedure___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Failed to register builtin RPC call handler for '"};
static const lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__0 = (const lean_object*)&l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__0_value;
static const lean_string_object l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__1 = (const lean_object*)&l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__1_value;
static const lean_string_object l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = ": only possible during initialization"};
static const lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__2 = (const lean_object*)&l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__2_value;
static const lean_closure_object l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__3 = (const lean_object*)&l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__3_value;
static const lean_closure_object l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__4 = (const lean_object*)&l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__4_value;
static const lean_string_object l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = ": already registered"};
static const lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__5 = (const lean_object*)&l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_registerRpcProcedure___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__0___boxed(lean_object*);
static const lean_string_object l_Lean_Server_registerRpcProcedure___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Server_registerRpcProcedure___lam__1___closed__0 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___lam__1___closed__0_value;
static const lean_string_object l_Lean_Server_registerRpcProcedure___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Server_registerRpcProcedure___lam__1___closed__1 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___lam__1___closed__1_value;
static const lean_string_object l_Lean_Server_registerRpcProcedure___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Server_registerRpcProcedure___lam__1___closed__2 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___lam__1___closed__2_value;
static const lean_string_object l_Lean_Server_registerRpcProcedure___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "wrapRpcProcedure"};
static const lean_object* l_Lean_Server_registerRpcProcedure___lam__1___closed__3 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___lam__1___closed__3_value;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___lam__1___closed__4;
static const lean_ctor_object l_Lean_Server_registerRpcProcedure___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_registerRpcProcedure___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(94, 250, 133, 113, 247, 228, 47, 148)}};
static const lean_object* l_Lean_Server_registerRpcProcedure___lam__1___closed__5 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___lam__1___closed__5_value;
static const lean_string_object l_Lean_Server_registerRpcProcedure___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Server_registerRpcProcedure___lam__1___closed__6 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Server_registerRpcProcedure___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_registerRpcProcedure___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Server_registerRpcProcedure___lam__1___closed__7 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___lam__1___closed__7_value;
static const lean_string_object l_Lean_Server_registerRpcProcedure___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Server_registerRpcProcedure___lam__1___closed__8 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___lam__1___closed__8_value;
static const lean_string_object l_Lean_Server_registerRpcProcedure___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Server_registerRpcProcedure___lam__1___closed__9 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___lam__1___closed__9_value;
static const lean_string_object l_Lean_Server_registerRpcProcedure___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l_Lean_Server_registerRpcProcedure___lam__1___closed__10 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___lam__1___closed__10_value;
static const lean_string_object l_Lean_Server_registerRpcProcedure___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Server_registerRpcProcedure___lam__1___closed__11 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___lam__1___closed__11_value;
static const lean_string_object l_Lean_Server_registerRpcProcedure___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Server_registerRpcProcedure___lam__1___closed__12 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___lam__1___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_registerRpcProcedure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerRpcProcedure___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerRpcProcedure___closed__0 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___closed__0_value;
static const lean_array_object l_Lean_Server_registerRpcProcedure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_registerRpcProcedure___closed__1 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___closed__1_value;
static const lean_ctor_object l_Lean_Server_registerRpcProcedure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 16, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_registerRpcProcedure___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_registerRpcProcedure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_registerRpcProcedure___closed__2 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___closed__2_value;
static const lean_ctor_object l_Lean_Server_registerRpcProcedure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_registerRpcProcedure___closed__3 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___closed__3_value;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Server_registerRpcProcedure___closed__4;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__5;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__6;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__7;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__8;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__9;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__10;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__11;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__12;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__13;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__14;
static const lean_ctor_object l_Lean_Server_registerRpcProcedure___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_registerRpcProcedure___closed__15 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___closed__15_value;
static const lean_string_object l_Lean_Server_registerRpcProcedure___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "_rpc_wrapped"};
static const lean_object* l_Lean_Server_registerRpcProcedure___closed__16 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___closed__16_value;
static const lean_ctor_object l_Lean_Server_registerRpcProcedure___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_registerRpcProcedure___closed__16_value),LEAN_SCALAR_PTR_LITERAL(76, 241, 252, 252, 247, 5, 133, 205)}};
static const lean_object* l_Lean_Server_registerRpcProcedure___closed__17 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___closed__17_value;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__18;
static const lean_string_object l_Lean_Server_registerRpcProcedure___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Failed to register RPC call handler for '"};
static const lean_object* l_Lean_Server_registerRpcProcedure___closed__19 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___closed__19_value;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__20;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__21;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__22;
static const lean_string_object l_Lean_Server_registerRpcProcedure___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = ": already registered (builtin)"};
static const lean_object* l_Lean_Server_registerRpcProcedure___closed__23 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___closed__23_value;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__24;
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 45, 83, 138, 97, 177, 55, 171)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rpc"};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 191, 146, 242, 66, 17, 254, 170)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__6_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "RequestHandling"};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__6_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__6_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__7_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__6_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 176, 141, 57, 104, 59, 134, 107)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__7_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__7_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__8_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__7_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(50, 79, 160, 227, 143, 147, 207, 26)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__8_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__8_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__9_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__8_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(179, 16, 93, 224, 35, 48, 178, 81)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__9_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__9_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__10_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__9_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(66, 254, 191, 69, 42, 47, 7, 49)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__10_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__10_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__11_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__11_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__11_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__12_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__10_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__11_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(183, 46, 61, 31, 170, 255, 2, 48)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__12_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__12_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__13_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__13_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__13_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__14_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__12_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__13_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(242, 15, 141, 148, 20, 126, 21, 236)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__14_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__14_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__15_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__14_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(115, 0, 134, 180, 68, 227, 15, 120)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__15_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__15_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__16_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__15_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(2, 233, 219, 132, 94, 69, 210, 55)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__16_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__16_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__17_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__16_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 228, 246, 136, 49, 138, 65, 188)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__17_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__17_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__18_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__17_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__6_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(114, 109, 58, 36, 225, 238, 44, 14)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__18_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__18_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__19_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__18_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1988373275) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(111, 146, 92, 49, 255, 161, 34, 122)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__19_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__19_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__20_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__20_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__20_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__21_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__19_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__20_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(100, 27, 52, 13, 161, 27, 9, 98)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__21_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__21_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__22_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__22_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__22_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__23_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__21_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__22_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(240, 109, 152, 143, 205, 193, 235, 11)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__23_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__23_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__24_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__23_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(161, 118, 63, 114, 178, 206, 159, 53)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__24_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__24_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__25_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "server_rpc_method"};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__25_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__25_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__26_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__25_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 27, 171, 148, 214, 45, 232, 98)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__26_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__26_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__27_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__26_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__27_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__27_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__28_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__26_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__28_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__28_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__29_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 209, .m_capacity = 209, .m_length = 202, .m_data = "Marks a function as a Lean server RPC method.\n    Shorthand for `registerRpcProcedure`.\n    The function must have type `α → RequestM (RequestTask β)` with\n    `[RpcEncodable α]` and `[RpcEncodable β]`."};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__29_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__29_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__30_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__24_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__26_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__29_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__30_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__30_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__31_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__30_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__27_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__28_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__31_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__31_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRpcProcedure_default___lam__0(uint64_t v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = l_Lean_Server_instInhabitedRequestError_default;
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRpcProcedure_default___lam__0___boxed(lean_object* v_x_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
uint64_t v_x_55__boxed_11_; lean_object* v_res_12_; 
v_x_55__boxed_11_ = lean_unbox_uint64(v_x_7_);
lean_dec_ref(v_x_7_);
v_res_12_ = l_Lean_Server_instInhabitedRpcProcedure_default___lam__0(v_x_55__boxed_11_, v___y_8_, v___y_9_);
lean_dec_ref(v___y_9_);
lean_dec(v___y_8_);
return v_res_12_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_16_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_20_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_);
v___x_21_ = lean_st_mk_ref(v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2____boxed(lean_object* v_a_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_();
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_25_, lean_object* v_x_26_){
_start:
{
if (lean_obj_tag(v_x_26_) == 0)
{
lean_object* v_k_27_; lean_object* v_v_28_; lean_object* v_l_29_; lean_object* v_r_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v_k_27_ = lean_ctor_get(v_x_26_, 1);
v_v_28_ = lean_ctor_get(v_x_26_, 2);
v_l_29_ = lean_ctor_get(v_x_26_, 3);
v_r_30_ = lean_ctor_get(v_x_26_, 4);
v___x_31_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0(v_init_25_, v_l_29_);
lean_inc(v_v_28_);
lean_inc(v_k_27_);
v___x_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_32_, 0, v_k_27_);
lean_ctor_set(v___x_32_, 1, v_v_28_);
v___x_33_ = lean_array_push(v___x_31_, v___x_32_);
v_init_25_ = v___x_33_;
v_x_26_ = v_r_30_;
goto _start;
}
else
{
return v_init_25_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_35_, lean_object* v_x_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0(v_init_35_, v_x_36_);
lean_dec(v_x_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1(lean_object* v_env_38_, lean_object* v_as_39_, size_t v_i_40_, size_t v_stop_41_, lean_object* v_b_42_){
_start:
{
lean_object* v___y_44_; uint8_t v___x_48_; 
v___x_48_ = lean_usize_dec_eq(v_i_40_, v_stop_41_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; lean_object* v_fst_50_; uint8_t v___x_51_; 
v___x_49_ = lean_array_uget_borrowed(v_as_39_, v_i_40_);
v_fst_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_fst_50_);
lean_inc_ref(v_env_38_);
v___x_51_ = l_Lean_Environment_contains(v_env_38_, v_fst_50_, v___x_48_);
if (v___x_51_ == 0)
{
v___y_44_ = v_b_42_;
goto v___jp_43_;
}
else
{
lean_object* v___x_52_; 
lean_inc(v___x_49_);
v___x_52_ = lean_array_push(v_b_42_, v___x_49_);
v___y_44_ = v___x_52_;
goto v___jp_43_;
}
}
else
{
lean_dec_ref(v_env_38_);
return v_b_42_;
}
v___jp_43_:
{
size_t v___x_45_; size_t v___x_46_; 
v___x_45_ = ((size_t)1ULL);
v___x_46_ = lean_usize_add(v_i_40_, v___x_45_);
v_i_40_ = v___x_46_;
v_b_42_ = v___y_44_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_53_, lean_object* v_as_54_, lean_object* v_i_55_, lean_object* v_stop_56_, lean_object* v_b_57_){
_start:
{
size_t v_i_boxed_58_; size_t v_stop_boxed_59_; lean_object* v_res_60_; 
v_i_boxed_58_ = lean_unbox_usize(v_i_55_);
lean_dec(v_i_55_);
v_stop_boxed_59_ = lean_unbox_usize(v_stop_56_);
lean_dec(v_stop_56_);
v_res_60_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1(v_env_53_, v_as_54_, v_i_boxed_58_, v_stop_boxed_59_, v_b_57_);
lean_dec_ref(v_as_54_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_(lean_object* v_env_67_, lean_object* v_s_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_71_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0(v___x_70_, v_s_68_);
v___x_72_ = lean_array_get_size(v___x_71_);
v___x_73_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_74_ = lean_nat_dec_lt(v___x_69_, v___x_72_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; 
lean_dec_ref(v___x_71_);
lean_dec_ref(v_env_67_);
v___x_75_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
return v___x_75_;
}
else
{
uint8_t v___x_76_; 
v___x_76_ = lean_nat_dec_le(v___x_72_, v___x_72_);
if (v___x_76_ == 0)
{
if (v___x_74_ == 0)
{
lean_object* v___x_77_; 
lean_dec_ref(v___x_71_);
lean_dec_ref(v_env_67_);
v___x_77_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
return v___x_77_;
}
else
{
size_t v___x_78_; size_t v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = ((size_t)0ULL);
v___x_79_ = lean_usize_of_nat(v___x_72_);
v___x_80_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1(v_env_67_, v___x_71_, v___x_78_, v___x_79_, v___x_73_);
lean_dec_ref(v___x_71_);
lean_inc_ref_n(v___x_80_, 2);
v___x_81_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
lean_ctor_set(v___x_81_, 2, v___x_80_);
return v___x_81_;
}
}
else
{
size_t v___x_82_; size_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_82_ = ((size_t)0ULL);
v___x_83_ = lean_usize_of_nat(v___x_72_);
v___x_84_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1(v_env_67_, v___x_71_, v___x_82_, v___x_83_, v___x_73_);
lean_dec_ref(v___x_71_);
lean_inc_ref_n(v___x_84_, 2);
v___x_85_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
lean_ctor_set(v___x_85_, 2, v___x_84_);
return v___x_85_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2____boxed(lean_object* v_env_86_, lean_object* v_s_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_(v_env_86_, v_s_87_);
lean_dec(v_s_87_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___f_100_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_101_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_102_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_103_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_101_, v___x_102_, v___f_100_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2____boxed(lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_();
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0(lean_object* v_init_106_, lean_object* v_t_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0(v_init_106_, v_t_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_109_, lean_object* v_t_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0(v_init_109_, v_t_110_);
lean_dec(v_t_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(lean_object* v_env_117_, lean_object* v_opts_118_, lean_object* v_procName_119_){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1));
v___x_121_ = l_Lean_Environment_evalConstCheck___redArg(v_env_117_, v_opts_118_, v___x_120_, v_procName_119_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___boxed(lean_object* v_env_122_, lean_object* v_opts_123_, lean_object* v_procName_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(v_env_122_, v_opts_123_, v_procName_124_);
lean_dec_ref(v_opts_123_);
return v_res_125_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_126_, lean_object* v_i_127_, lean_object* v_k_128_){
_start:
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = lean_array_get_size(v_keys_126_);
v___x_130_ = lean_nat_dec_lt(v_i_127_, v___x_129_);
if (v___x_130_ == 0)
{
lean_dec(v_i_127_);
return v___x_130_;
}
else
{
lean_object* v_k_x27_131_; uint8_t v___x_132_; 
v_k_x27_131_ = lean_array_fget_borrowed(v_keys_126_, v_i_127_);
v___x_132_ = lean_name_eq(v_k_128_, v_k_x27_131_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_unsigned_to_nat(1u);
v___x_134_ = lean_nat_add(v_i_127_, v___x_133_);
lean_dec(v_i_127_);
v_i_127_ = v___x_134_;
goto _start;
}
else
{
lean_dec(v_i_127_);
return v___x_132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_136_, lean_object* v_i_137_, lean_object* v_k_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg(v_keys_136_, v_i_137_, v_k_138_);
lean_dec(v_k_138_);
lean_dec_ref(v_keys_136_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_141_; size_t v___x_142_; size_t v___x_143_; 
v___x_141_ = ((size_t)5ULL);
v___x_142_ = ((size_t)1ULL);
v___x_143_ = lean_usize_shift_left(v___x_142_, v___x_141_);
return v___x_143_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; 
v___x_144_ = ((size_t)1ULL);
v___x_145_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__0);
v___x_146_ = lean_usize_sub(v___x_145_, v___x_144_);
return v___x_146_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg(lean_object* v_x_147_, size_t v_x_148_, lean_object* v_x_149_){
_start:
{
if (lean_obj_tag(v_x_147_) == 0)
{
lean_object* v_es_150_; lean_object* v___x_151_; size_t v___x_152_; size_t v___x_153_; size_t v___x_154_; lean_object* v_j_155_; lean_object* v___x_156_; 
v_es_150_ = lean_ctor_get(v_x_147_, 0);
v___x_151_ = lean_box(2);
v___x_152_ = ((size_t)5ULL);
v___x_153_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1);
v___x_154_ = lean_usize_land(v_x_148_, v___x_153_);
v_j_155_ = lean_usize_to_nat(v___x_154_);
v___x_156_ = lean_array_get_borrowed(v___x_151_, v_es_150_, v_j_155_);
lean_dec(v_j_155_);
switch(lean_obj_tag(v___x_156_))
{
case 0:
{
lean_object* v_key_157_; uint8_t v___x_158_; 
v_key_157_ = lean_ctor_get(v___x_156_, 0);
v___x_158_ = lean_name_eq(v_x_149_, v_key_157_);
return v___x_158_;
}
case 1:
{
lean_object* v_node_159_; size_t v___x_160_; 
v_node_159_ = lean_ctor_get(v___x_156_, 0);
v___x_160_ = lean_usize_shift_right(v_x_148_, v___x_152_);
v_x_147_ = v_node_159_;
v_x_148_ = v___x_160_;
goto _start;
}
default: 
{
uint8_t v___x_162_; 
v___x_162_ = 0;
return v___x_162_;
}
}
}
else
{
lean_object* v_ks_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v_ks_163_ = lean_ctor_get(v_x_147_, 0);
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg(v_ks_163_, v___x_164_, v_x_149_);
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___boxed(lean_object* v_x_166_, lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
size_t v_x_253__boxed_169_; uint8_t v_res_170_; lean_object* v_r_171_; 
v_x_253__boxed_169_ = lean_unbox_usize(v_x_167_);
lean_dec(v_x_167_);
v_res_170_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg(v_x_166_, v_x_253__boxed_169_, v_x_168_);
lean_dec(v_x_168_);
lean_dec_ref(v_x_166_);
v_r_171_ = lean_box(v_res_170_);
return v_r_171_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_172_; uint64_t v___x_173_; 
v___x_172_ = lean_unsigned_to_nat(1723u);
v___x_173_ = lean_uint64_of_nat(v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
uint64_t v___y_177_; 
if (lean_obj_tag(v_x_175_) == 0)
{
uint64_t v___x_180_; 
v___x_180_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___closed__0);
v___y_177_ = v___x_180_;
goto v___jp_176_;
}
else
{
uint64_t v_hash_181_; 
v_hash_181_ = lean_ctor_get_uint64(v_x_175_, sizeof(void*)*2);
v___y_177_ = v_hash_181_;
goto v___jp_176_;
}
v___jp_176_:
{
size_t v___x_178_; uint8_t v___x_179_; 
v___x_178_ = lean_uint64_to_usize(v___y_177_);
v___x_179_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg(v_x_174_, v___x_178_, v_x_175_);
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___boxed(lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
uint8_t v_res_184_; lean_object* v_r_185_; 
v_res_184_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(v_x_182_, v_x_183_);
lean_dec(v_x_183_);
lean_dec_ref(v_x_182_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_existsBuiltinRpcProcedure(lean_object* v_method_186_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_188_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_189_ = lean_st_ref_get(v___x_188_);
v___x_190_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(v___x_189_, v_method_186_);
lean_dec(v___x_189_);
v___x_191_ = lean_box(v___x_190_);
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_existsBuiltinRpcProcedure___boxed(lean_object* v_method_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Server_existsBuiltinRpcProcedure(v_method_193_);
lean_dec(v_method_193_);
return v_res_195_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0(lean_object* v_00_u03b2_196_, lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
uint8_t v___x_199_; 
v___x_199_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(v_x_197_, v_x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___boxed(lean_object* v_00_u03b2_200_, lean_object* v_x_201_, lean_object* v_x_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0(v_00_u03b2_200_, v_x_201_, v_x_202_);
lean_dec(v_x_202_);
lean_dec_ref(v_x_201_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0(lean_object* v_00_u03b2_205_, lean_object* v_x_206_, size_t v_x_207_, lean_object* v_x_208_){
_start:
{
uint8_t v___x_209_; 
v___x_209_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg(v_x_206_, v_x_207_, v_x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___boxed(lean_object* v_00_u03b2_210_, lean_object* v_x_211_, lean_object* v_x_212_, lean_object* v_x_213_){
_start:
{
size_t v_x_343__boxed_214_; uint8_t v_res_215_; lean_object* v_r_216_; 
v_x_343__boxed_214_ = lean_unbox_usize(v_x_212_);
lean_dec(v_x_212_);
v_res_215_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0(v_00_u03b2_210_, v_x_211_, v_x_343__boxed_214_, v_x_213_);
lean_dec(v_x_213_);
lean_dec_ref(v_x_211_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_217_, lean_object* v_keys_218_, lean_object* v_vals_219_, lean_object* v_heq_220_, lean_object* v_i_221_, lean_object* v_k_222_){
_start:
{
uint8_t v___x_223_; 
v___x_223_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg(v_keys_218_, v_i_221_, v_k_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_224_, lean_object* v_keys_225_, lean_object* v_vals_226_, lean_object* v_heq_227_, lean_object* v_i_228_, lean_object* v_k_229_){
_start:
{
uint8_t v_res_230_; lean_object* v_r_231_; 
v_res_230_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1(v_00_u03b2_224_, v_keys_225_, v_vals_226_, v_heq_227_, v_i_228_, v_k_229_);
lean_dec(v_k_229_);
lean_dec_ref(v_vals_226_);
lean_dec_ref(v_keys_225_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1(lean_object* v___y_232_){
_start:
{
lean_object* v_doc_234_; lean_object* v___x_235_; 
v_doc_234_ = lean_ctor_get(v___y_232_, 1);
lean_inc_ref(v_doc_234_);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v_doc_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1___boxed(lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1(v___y_236_);
lean_dec_ref(v___y_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__0(lean_object* v_val_239_, uint64_t v_sessionId_240_, lean_object* v_params_241_, lean_object* v___y_242_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_box_uint64(v_sessionId_240_);
lean_inc_ref(v___y_242_);
v___x_245_ = lean_apply_4(v_val_239_, v___x_244_, v_params_241_, v___y_242_, lean_box(0));
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_259_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_259_ == 0)
{
v___x_248_ = v___x_245_;
v_isShared_249_ = v_isSharedCheck_259_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_245_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_259_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; 
v___x_250_ = lean_io_wait(v_a_246_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_253_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
lean_dec_ref(v___x_250_);
if (v_isShared_249_ == 0)
{
lean_ctor_set_tag(v___x_248_, 1);
lean_ctor_set(v___x_248_, 0, v_a_251_);
v___x_253_ = v___x_248_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; 
v_a_255_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_255_);
lean_dec_ref(v___x_250_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v_a_255_);
v___x_257_ = v___x_248_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
else
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
v_a_260_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v___x_245_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_245_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_260_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__0___boxed(lean_object* v_val_268_, lean_object* v_sessionId_269_, lean_object* v_params_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
uint64_t v_sessionId_boxed_273_; lean_object* v_res_274_; 
v_sessionId_boxed_273_ = lean_unbox_uint64(v_sessionId_269_);
lean_dec_ref(v_sessionId_269_);
v_res_274_ = l_Lean_Server_handleRpcCall___lam__0(v_val_268_, v_sessionId_boxed_273_, v_params_270_, v___y_271_);
lean_dec_ref(v___y_271_);
return v_res_274_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_handleRpcCall___lam__1(lean_object* v___x_275_, lean_object* v___x_276_, lean_object* v_method_277_, lean_object* v_s_278_){
_start:
{
lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_279_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_278_);
v___x_280_ = lean_nat_dec_le(v___x_275_, v___x_279_);
lean_dec(v___x_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v_toEnvExtension_282_; lean_object* v_asyncMode_283_; lean_object* v___x_284_; uint8_t v___x_285_; lean_object* v___x_286_; 
v___x_281_ = l_Lean_Server_userRpcProcedures;
v_toEnvExtension_282_ = lean_ctor_get(v___x_281_, 0);
v_asyncMode_283_ = lean_ctor_get(v_toEnvExtension_282_, 2);
v___x_284_ = l_Lean_Server_Snapshots_Snapshot_env(v_s_278_);
v___x_285_ = 0;
v___x_286_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_276_, v___x_281_, v___x_284_, v_method_277_, v_asyncMode_283_, v___x_285_);
if (lean_obj_tag(v___x_286_) == 0)
{
return v___x_280_;
}
else
{
uint8_t v___x_287_; 
lean_dec_ref(v___x_286_);
v___x_287_ = 1;
return v___x_287_;
}
}
else
{
lean_dec(v_method_277_);
lean_dec(v___x_276_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__1___boxed(lean_object* v___x_288_, lean_object* v___x_289_, lean_object* v_method_290_, lean_object* v_s_291_){
_start:
{
uint8_t v_res_292_; lean_object* v_r_293_; 
v_res_292_ = l_Lean_Server_handleRpcCall___lam__1(v___x_288_, v___x_289_, v_method_290_, v_s_291_);
lean_dec_ref(v_s_291_);
lean_dec(v___x_288_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__2(lean_object* v___x_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_294_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__2___boxed(lean_object* v___x_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Server_handleRpcCall___lam__2(v___x_298_, v___y_299_);
lean_dec_ref(v___y_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__3(lean_object* v___x_304_, lean_object* v_method_305_, lean_object* v___x_306_, uint8_t v___x_307_, uint64_t v_sessionId_308_, lean_object* v_params_309_, lean_object* v___x_310_, lean_object* v_snap_311_, lean_object* v___y_312_){
_start:
{
lean_object* v___x_314_; lean_object* v_toEnvExtension_315_; lean_object* v_asyncMode_316_; lean_object* v___x_317_; uint8_t v___x_318_; lean_object* v___x_319_; 
v___x_314_ = l_Lean_Server_userRpcProcedures;
v_toEnvExtension_315_ = lean_ctor_get(v___x_314_, 0);
v_asyncMode_316_ = lean_ctor_get(v_toEnvExtension_315_, 2);
v___x_317_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_311_);
v___x_318_ = 0;
lean_inc_ref(v___x_317_);
v___x_319_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_304_, v___x_314_, v___x_317_, v_method_305_, v_asyncMode_316_, v___x_318_);
if (lean_obj_tag(v___x_319_) == 1)
{
lean_object* v_cmdState_320_; lean_object* v_val_321_; lean_object* v_scopes_322_; lean_object* v___x_323_; lean_object* v_opts_324_; lean_object* v___x_325_; 
lean_dec_ref(v___x_310_);
v_cmdState_320_ = lean_ctor_get(v_snap_311_, 2);
v_val_321_ = lean_ctor_get(v___x_319_, 0);
lean_inc_n(v_val_321_, 2);
lean_dec_ref(v___x_319_);
v_scopes_322_ = lean_ctor_get(v_cmdState_320_, 2);
v___x_323_ = l_List_head_x21___redArg(v___x_306_, v_scopes_322_);
v_opts_324_ = lean_ctor_get(v___x_323_, 1);
lean_inc_ref(v_opts_324_);
lean_dec(v___x_323_);
v___x_325_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(v___x_317_, v_opts_324_, v_val_321_);
lean_dec_ref(v_opts_324_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_341_; 
lean_dec(v_params_309_);
v_a_326_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_341_ == 0)
{
v___x_328_ = v___x_325_;
v_isShared_329_ = v_isSharedCheck_341_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_341_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
uint8_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_330_ = 4;
v___x_331_ = ((lean_object*)(l_Lean_Server_handleRpcCall___lam__3___closed__0));
v___x_332_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_321_, v___x_307_);
v___x_333_ = lean_string_append(v___x_331_, v___x_332_);
lean_dec_ref(v___x_332_);
v___x_334_ = ((lean_object*)(l_Lean_Server_handleRpcCall___lam__3___closed__1));
v___x_335_ = lean_string_append(v___x_333_, v___x_334_);
v___x_336_ = lean_string_append(v___x_335_, v_a_326_);
lean_dec(v_a_326_);
v___x_337_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set_uint8(v___x_337_, sizeof(void*)*1, v___x_330_);
if (v_isShared_329_ == 0)
{
lean_ctor_set_tag(v___x_328_, 1);
lean_ctor_set(v___x_328_, 0, v___x_337_);
v___x_339_ = v___x_328_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
else
{
lean_object* v_a_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec(v_val_321_);
v_a_342_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_342_);
lean_dec_ref(v___x_325_);
v___x_343_ = lean_box_uint64(v_sessionId_308_);
lean_inc_ref(v___y_312_);
v___x_344_ = lean_apply_4(v_a_342_, v___x_343_, v_params_309_, v___y_312_, lean_box(0));
return v___x_344_;
}
}
else
{
lean_object* v___x_345_; 
lean_dec(v___x_319_);
lean_dec_ref(v___x_317_);
lean_dec(v_params_309_);
v___x_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_310_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__3___boxed(lean_object* v___x_346_, lean_object* v_method_347_, lean_object* v___x_348_, lean_object* v___x_349_, lean_object* v_sessionId_350_, lean_object* v_params_351_, lean_object* v___x_352_, lean_object* v_snap_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
uint8_t v___x_2331__boxed_356_; uint64_t v_sessionId_boxed_357_; lean_object* v_res_358_; 
v___x_2331__boxed_356_ = lean_unbox(v___x_349_);
v_sessionId_boxed_357_ = lean_unbox_uint64(v_sessionId_350_);
lean_dec_ref(v_sessionId_350_);
v_res_358_ = l_Lean_Server_handleRpcCall___lam__3(v___x_346_, v_method_347_, v___x_348_, v___x_2331__boxed_356_, v_sessionId_boxed_357_, v_params_351_, v___x_352_, v_snap_353_, v___y_354_);
lean_dec_ref(v___y_354_);
lean_dec_ref(v_snap_353_);
lean_dec_ref(v___x_348_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_359_, lean_object* v_vals_360_, lean_object* v_i_361_, lean_object* v_k_362_){
_start:
{
lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_363_ = lean_array_get_size(v_keys_359_);
v___x_364_ = lean_nat_dec_lt(v_i_361_, v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
lean_dec(v_i_361_);
v___x_365_ = lean_box(0);
return v___x_365_;
}
else
{
lean_object* v_k_x27_366_; uint8_t v___x_367_; 
v_k_x27_366_ = lean_array_fget_borrowed(v_keys_359_, v_i_361_);
v___x_367_ = lean_name_eq(v_k_362_, v_k_x27_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_unsigned_to_nat(1u);
v___x_369_ = lean_nat_add(v_i_361_, v___x_368_);
lean_dec(v_i_361_);
v_i_361_ = v___x_369_;
goto _start;
}
else
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_array_fget_borrowed(v_vals_360_, v_i_361_);
lean_dec(v_i_361_);
lean_inc(v___x_371_);
v___x_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
return v___x_372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_373_, lean_object* v_vals_374_, lean_object* v_i_375_, lean_object* v_k_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(v_keys_373_, v_vals_374_, v_i_375_, v_k_376_);
lean_dec(v_k_376_);
lean_dec_ref(v_vals_374_);
lean_dec_ref(v_keys_373_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(lean_object* v_x_378_, size_t v_x_379_, lean_object* v_x_380_){
_start:
{
if (lean_obj_tag(v_x_378_) == 0)
{
lean_object* v_es_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_402_; 
v_es_381_ = lean_ctor_get(v_x_378_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v_x_378_);
if (v_isSharedCheck_402_ == 0)
{
v___x_383_ = v_x_378_;
v_isShared_384_ = v_isSharedCheck_402_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_es_381_);
lean_dec(v_x_378_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_402_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; size_t v___x_386_; size_t v___x_387_; size_t v___x_388_; lean_object* v_j_389_; lean_object* v___x_390_; 
v___x_385_ = lean_box(2);
v___x_386_ = ((size_t)5ULL);
v___x_387_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1);
v___x_388_ = lean_usize_land(v_x_379_, v___x_387_);
v_j_389_ = lean_usize_to_nat(v___x_388_);
v___x_390_ = lean_array_get(v___x_385_, v_es_381_, v_j_389_);
lean_dec(v_j_389_);
lean_dec_ref(v_es_381_);
switch(lean_obj_tag(v___x_390_))
{
case 0:
{
lean_object* v_key_391_; lean_object* v_val_392_; uint8_t v___x_393_; 
v_key_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_key_391_);
v_val_392_ = lean_ctor_get(v___x_390_, 1);
lean_inc(v_val_392_);
lean_dec_ref(v___x_390_);
v___x_393_ = lean_name_eq(v_x_380_, v_key_391_);
lean_dec(v_key_391_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
lean_dec(v_val_392_);
lean_del_object(v___x_383_);
v___x_394_ = lean_box(0);
return v___x_394_;
}
else
{
lean_object* v___x_396_; 
if (v_isShared_384_ == 0)
{
lean_ctor_set_tag(v___x_383_, 1);
lean_ctor_set(v___x_383_, 0, v_val_392_);
v___x_396_ = v___x_383_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_val_392_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
case 1:
{
lean_object* v_node_398_; size_t v___x_399_; 
lean_del_object(v___x_383_);
v_node_398_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_node_398_);
lean_dec_ref(v___x_390_);
v___x_399_ = lean_usize_shift_right(v_x_379_, v___x_386_);
v_x_378_ = v_node_398_;
v_x_379_ = v___x_399_;
goto _start;
}
default: 
{
lean_object* v___x_401_; 
lean_del_object(v___x_383_);
v___x_401_ = lean_box(0);
return v___x_401_;
}
}
}
}
else
{
lean_object* v_ks_403_; lean_object* v_vs_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_ks_403_ = lean_ctor_get(v_x_378_, 0);
lean_inc_ref(v_ks_403_);
v_vs_404_ = lean_ctor_get(v_x_378_, 1);
lean_inc_ref(v_vs_404_);
lean_dec_ref(v_x_378_);
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(v_ks_403_, v_vs_404_, v___x_405_, v_x_380_);
lean_dec_ref(v_vs_404_);
lean_dec_ref(v_ks_403_);
return v___x_406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg___boxed(lean_object* v_x_407_, lean_object* v_x_408_, lean_object* v_x_409_){
_start:
{
size_t v_x_2428__boxed_410_; lean_object* v_res_411_; 
v_x_2428__boxed_410_ = lean_unbox_usize(v_x_408_);
lean_dec(v_x_408_);
v_res_411_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(v_x_407_, v_x_2428__boxed_410_, v_x_409_);
lean_dec(v_x_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(lean_object* v_x_412_, lean_object* v_x_413_){
_start:
{
uint64_t v___y_415_; 
if (lean_obj_tag(v_x_413_) == 0)
{
uint64_t v___x_418_; 
v___x_418_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___closed__0);
v___y_415_ = v___x_418_;
goto v___jp_414_;
}
else
{
uint64_t v_hash_419_; 
v_hash_419_ = lean_ctor_get_uint64(v_x_413_, sizeof(void*)*2);
v___y_415_ = v_hash_419_;
goto v___jp_414_;
}
v___jp_414_:
{
size_t v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_uint64_to_usize(v___y_415_);
v___x_417_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(v_x_412_, v___x_416_, v_x_413_);
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg___boxed(lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(v_x_420_, v_x_421_);
lean_dec(v_x_421_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall(lean_object* v_p_425_, lean_object* v_a_426_){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v_toTextDocumentPositionParams_430_; uint64_t v_sessionId_431_; lean_object* v_method_432_; lean_object* v_params_433_; lean_object* v___x_434_; 
v___x_428_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_429_ = lean_st_ref_get(v___x_428_);
v_toTextDocumentPositionParams_430_ = lean_ctor_get(v_p_425_, 0);
lean_inc_ref(v_toTextDocumentPositionParams_430_);
v_sessionId_431_ = lean_ctor_get_uint64(v_p_425_, sizeof(void*)*3);
v_method_432_ = lean_ctor_get(v_p_425_, 1);
lean_inc(v_method_432_);
v_params_433_ = lean_ctor_get(v_p_425_, 2);
lean_inc(v_params_433_);
lean_dec_ref(v_p_425_);
v___x_434_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(v___x_429_, v_method_432_);
if (lean_obj_tag(v___x_434_) == 1)
{
lean_object* v_val_435_; lean_object* v___x_436_; lean_object* v___f_437_; lean_object* v___x_438_; 
lean_dec(v_method_432_);
lean_dec_ref(v_toTextDocumentPositionParams_430_);
v_val_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_val_435_);
lean_dec_ref(v___x_434_);
v___x_436_ = lean_box_uint64(v_sessionId_431_);
v___f_437_ = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__0___boxed), 5, 3);
lean_closure_set(v___f_437_, 0, v_val_435_);
lean_closure_set(v___f_437_, 1, v___x_436_);
lean_closure_set(v___f_437_, 2, v_params_433_);
v___x_438_ = l_Lean_Server_RequestM_asTask___redArg(v___f_437_, v_a_426_);
return v___x_438_;
}
else
{
lean_object* v___x_439_; lean_object* v_a_440_; lean_object* v_toEditableDocumentCore_441_; lean_object* v_meta_442_; lean_object* v_text_443_; lean_object* v_position_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___f_448_; uint8_t v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___f_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___f_460_; lean_object* v___x_461_; 
lean_dec(v___x_434_);
v___x_439_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1(v_a_426_);
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref(v___x_439_);
v_toEditableDocumentCore_441_ = lean_ctor_get(v_a_440_, 0);
v_meta_442_ = lean_ctor_get(v_toEditableDocumentCore_441_, 0);
v_text_443_ = lean_ctor_get(v_meta_442_, 3);
v_position_444_ = lean_ctor_get(v_toTextDocumentPositionParams_430_, 1);
lean_inc_ref(v_position_444_);
lean_dec_ref(v_toTextDocumentPositionParams_430_);
v___x_445_ = lean_box(0);
v___x_446_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_447_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_443_, v_position_444_);
lean_inc_n(v_method_432_, 2);
v___f_448_ = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__1___boxed), 4, 3);
lean_closure_set(v___f_448_, 0, v___x_447_);
lean_closure_set(v___f_448_, 1, v___x_445_);
lean_closure_set(v___f_448_, 2, v_method_432_);
v___x_449_ = 2;
v___x_450_ = ((lean_object*)(l_Lean_Server_handleRpcCall___closed__0));
v___x_451_ = 1;
v___x_452_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_432_, v___x_451_);
v___x_453_ = lean_string_append(v___x_450_, v___x_452_);
lean_dec_ref(v___x_452_);
v___x_454_ = ((lean_object*)(l_Lean_Server_handleRpcCall___closed__1));
v___x_455_ = lean_string_append(v___x_453_, v___x_454_);
v___x_456_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set_uint8(v___x_456_, sizeof(void*)*1, v___x_449_);
lean_inc_ref(v___x_456_);
v___f_457_ = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__2___boxed), 3, 1);
lean_closure_set(v___f_457_, 0, v___x_456_);
v___x_458_ = lean_box(v___x_451_);
v___x_459_ = lean_box_uint64(v_sessionId_431_);
v___f_460_ = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__3___boxed), 10, 7);
lean_closure_set(v___f_460_, 0, v___x_445_);
lean_closure_set(v___f_460_, 1, v_method_432_);
lean_closure_set(v___f_460_, 2, v___x_446_);
lean_closure_set(v___f_460_, 3, v___x_458_);
lean_closure_set(v___f_460_, 4, v___x_459_);
lean_closure_set(v___f_460_, 5, v_params_433_);
lean_closure_set(v___f_460_, 6, v___x_456_);
v___x_461_ = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(v_a_440_, v___f_448_, v___f_457_, v___f_460_, v_a_426_);
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___boxed(lean_object* v_p_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Server_handleRpcCall(v_p_462_, v_a_463_);
lean_dec_ref(v_a_463_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0(lean_object* v_00_u03b2_466_, lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(v_x_467_, v_x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___boxed(lean_object* v_00_u03b2_470_, lean_object* v_x_471_, lean_object* v_x_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0(v_00_u03b2_470_, v_x_471_, v_x_472_);
lean_dec(v_x_472_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0(lean_object* v_00_u03b2_474_, lean_object* v_x_475_, size_t v_x_476_, lean_object* v_x_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(v_x_475_, v_x_476_, v_x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___boxed(lean_object* v_00_u03b2_479_, lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_x_482_){
_start:
{
size_t v_x_2578__boxed_483_; lean_object* v_res_484_; 
v_x_2578__boxed_483_ = lean_unbox_usize(v_x_481_);
lean_dec(v_x_481_);
v_res_484_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0(v_00_u03b2_479_, v_x_480_, v_x_2578__boxed_483_, v_x_482_);
lean_dec(v_x_482_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_485_, lean_object* v_keys_486_, lean_object* v_vals_487_, lean_object* v_heq_488_, lean_object* v_i_489_, lean_object* v_k_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(v_keys_486_, v_vals_487_, v_i_489_, v_k_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_492_, lean_object* v_keys_493_, lean_object* v_vals_494_, lean_object* v_heq_495_, lean_object* v_i_496_, lean_object* v_k_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2(v_00_u03b2_492_, v_keys_493_, v_vals_494_, v_heq_495_, v_i_496_, v_k_497_);
lean_dec(v_k_497_);
lean_dec_ref(v_vals_494_);
lean_dec_ref(v_keys_493_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_499_, uint8_t v_a_500_, lean_object* v___y_501_){
_start:
{
if (lean_obj_tag(v___y_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_dec(v_serialize_x3f_499_);
v_a_502_ = lean_ctor_get(v___y_501_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___y_501_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___y_501_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___y_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
else
{
if (lean_obj_tag(v_serialize_x3f_499_) == 1)
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_521_; 
v_a_510_ = lean_ctor_get(v___y_501_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___y_501_);
if (v_isSharedCheck_521_ == 0)
{
v___x_512_ = v___y_501_;
v_isShared_513_ = v_isSharedCheck_521_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___y_501_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_521_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v_val_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v_val_514_ = lean_ctor_get(v_serialize_x3f_499_, 0);
lean_inc(v_val_514_);
lean_dec_ref(v_serialize_x3f_499_);
v___x_515_ = lean_box(0);
v___x_516_ = lean_apply_1(v_val_514_, v_a_510_);
v___x_517_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
lean_ctor_set_uint8(v___x_517_, sizeof(void*)*2, v_a_500_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_517_);
v___x_519_ = v___x_512_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_532_; 
lean_dec(v_serialize_x3f_499_);
v_a_522_ = lean_ctor_get(v___y_501_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___y_501_);
if (v_isSharedCheck_532_ == 0)
{
v___x_524_ = v___y_501_;
v_isShared_525_ = v_isSharedCheck_532_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___y_501_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_532_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
lean_inc(v_a_522_);
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v_a_522_);
v___x_527_ = l_Lean_Json_compress(v_a_522_);
v___x_528_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_528_, 0, v___x_526_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*2, v_a_500_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_528_);
v___x_530_ = v___x_524_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_533_, lean_object* v_a_534_, lean_object* v___y_535_){
_start:
{
uint8_t v_a_666__boxed_536_; lean_object* v_res_537_; 
v_a_666__boxed_536_ = lean_unbox(v_a_534_);
v_res_537_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_533_, v_a_666__boxed_536_, v___y_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8___redArg(lean_object* v_x_538_, lean_object* v_x_539_, lean_object* v_x_540_, lean_object* v_x_541_){
_start:
{
lean_object* v_ks_542_; lean_object* v_vs_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_567_; 
v_ks_542_ = lean_ctor_get(v_x_538_, 0);
v_vs_543_ = lean_ctor_get(v_x_538_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_567_ == 0)
{
v___x_545_ = v_x_538_;
v_isShared_546_ = v_isSharedCheck_567_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_vs_543_);
lean_inc(v_ks_542_);
lean_dec(v_x_538_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_567_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_547_ = lean_array_get_size(v_ks_542_);
v___x_548_ = lean_nat_dec_lt(v_x_539_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
lean_dec(v_x_539_);
v___x_549_ = lean_array_push(v_ks_542_, v_x_540_);
v___x_550_ = lean_array_push(v_vs_543_, v_x_541_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 1, v___x_550_);
lean_ctor_set(v___x_545_, 0, v___x_549_);
v___x_552_ = v___x_545_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
else
{
lean_object* v_k_x27_554_; uint8_t v___x_555_; 
v_k_x27_554_ = lean_array_fget_borrowed(v_ks_542_, v_x_539_);
v___x_555_ = lean_string_dec_eq(v_x_540_, v_k_x27_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_557_; 
if (v_isShared_546_ == 0)
{
v___x_557_ = v___x_545_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_ks_542_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_vs_543_);
v___x_557_ = v_reuseFailAlloc_561_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_unsigned_to_nat(1u);
v___x_559_ = lean_nat_add(v_x_539_, v___x_558_);
lean_dec(v_x_539_);
v_x_538_ = v___x_557_;
v_x_539_ = v___x_559_;
goto _start;
}
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_562_ = lean_array_fset(v_ks_542_, v_x_539_, v_x_540_);
v___x_563_ = lean_array_fset(v_vs_543_, v_x_539_, v_x_541_);
lean_dec(v_x_539_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 1, v___x_563_);
lean_ctor_set(v___x_545_, 0, v___x_562_);
v___x_565_ = v___x_545_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7___redArg(lean_object* v_n_568_, lean_object* v_k_569_, lean_object* v_v_570_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8___redArg(v_n_568_, v___x_571_, v_k_569_, v_v_570_);
return v___x_572_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* v_x_574_, size_t v_x_575_, size_t v_x_576_, lean_object* v_x_577_, lean_object* v_x_578_){
_start:
{
if (lean_obj_tag(v_x_574_) == 0)
{
lean_object* v_es_579_; size_t v___x_580_; size_t v___x_581_; size_t v___x_582_; size_t v___x_583_; lean_object* v_j_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v_es_579_ = lean_ctor_get(v_x_574_, 0);
v___x_580_ = ((size_t)5ULL);
v___x_581_ = ((size_t)1ULL);
v___x_582_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1);
v___x_583_ = lean_usize_land(v_x_575_, v___x_582_);
v_j_584_ = lean_usize_to_nat(v___x_583_);
v___x_585_ = lean_array_get_size(v_es_579_);
v___x_586_ = lean_nat_dec_lt(v_j_584_, v___x_585_);
if (v___x_586_ == 0)
{
lean_dec(v_j_584_);
lean_dec(v_x_578_);
lean_dec_ref(v_x_577_);
return v_x_574_;
}
else
{
lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_623_; 
lean_inc_ref(v_es_579_);
v_isSharedCheck_623_ = !lean_is_exclusive(v_x_574_);
if (v_isSharedCheck_623_ == 0)
{
lean_object* v_unused_624_; 
v_unused_624_ = lean_ctor_get(v_x_574_, 0);
lean_dec(v_unused_624_);
v___x_588_ = v_x_574_;
v_isShared_589_ = v_isSharedCheck_623_;
goto v_resetjp_587_;
}
else
{
lean_dec(v_x_574_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_623_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_v_590_; lean_object* v___x_591_; lean_object* v_xs_x27_592_; lean_object* v___y_594_; 
v_v_590_ = lean_array_fget(v_es_579_, v_j_584_);
v___x_591_ = lean_box(0);
v_xs_x27_592_ = lean_array_fset(v_es_579_, v_j_584_, v___x_591_);
switch(lean_obj_tag(v_v_590_))
{
case 0:
{
lean_object* v_key_599_; lean_object* v_val_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_610_; 
v_key_599_ = lean_ctor_get(v_v_590_, 0);
v_val_600_ = lean_ctor_get(v_v_590_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_v_590_);
if (v_isSharedCheck_610_ == 0)
{
v___x_602_ = v_v_590_;
v_isShared_603_ = v_isSharedCheck_610_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_val_600_);
lean_inc(v_key_599_);
lean_dec(v_v_590_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_610_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
uint8_t v___x_604_; 
v___x_604_ = lean_string_dec_eq(v_x_577_, v_key_599_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; 
lean_del_object(v___x_602_);
v___x_605_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_599_, v_val_600_, v_x_577_, v_x_578_);
v___x_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
v___y_594_ = v___x_606_;
goto v___jp_593_;
}
else
{
lean_object* v___x_608_; 
lean_dec(v_val_600_);
lean_dec(v_key_599_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 1, v_x_578_);
lean_ctor_set(v___x_602_, 0, v_x_577_);
v___x_608_ = v___x_602_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_x_577_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_x_578_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
v___y_594_ = v___x_608_;
goto v___jp_593_;
}
}
}
}
case 1:
{
lean_object* v_node_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_621_; 
v_node_611_ = lean_ctor_get(v_v_590_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v_v_590_);
if (v_isSharedCheck_621_ == 0)
{
v___x_613_ = v_v_590_;
v_isShared_614_ = v_isSharedCheck_621_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_node_611_);
lean_dec(v_v_590_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_621_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
size_t v___x_615_; size_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_615_ = lean_usize_shift_right(v_x_575_, v___x_580_);
v___x_616_ = lean_usize_add(v_x_576_, v___x_581_);
v___x_617_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_node_611_, v___x_615_, v___x_616_, v_x_577_, v_x_578_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_617_);
v___x_619_ = v___x_613_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
v___y_594_ = v___x_619_;
goto v___jp_593_;
}
}
}
default: 
{
lean_object* v___x_622_; 
v___x_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_622_, 0, v_x_577_);
lean_ctor_set(v___x_622_, 1, v_x_578_);
v___y_594_ = v___x_622_;
goto v___jp_593_;
}
}
v___jp_593_:
{
lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_595_ = lean_array_fset(v_xs_x27_592_, v_j_584_, v___y_594_);
lean_dec(v_j_584_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_595_);
v___x_597_ = v___x_588_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
else
{
lean_object* v_ks_625_; lean_object* v_vs_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_646_; 
v_ks_625_ = lean_ctor_get(v_x_574_, 0);
v_vs_626_ = lean_ctor_get(v_x_574_, 1);
v_isSharedCheck_646_ = !lean_is_exclusive(v_x_574_);
if (v_isSharedCheck_646_ == 0)
{
v___x_628_ = v_x_574_;
v_isShared_629_ = v_isSharedCheck_646_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_vs_626_);
lean_inc(v_ks_625_);
lean_dec(v_x_574_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_646_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_ks_625_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_vs_626_);
v___x_631_ = v_reuseFailAlloc_645_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v_newNode_632_; uint8_t v___y_634_; size_t v___x_640_; uint8_t v___x_641_; 
v_newNode_632_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7___redArg(v___x_631_, v_x_577_, v_x_578_);
v___x_640_ = ((size_t)7ULL);
v___x_641_ = lean_usize_dec_le(v___x_640_, v_x_576_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_642_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_632_);
v___x_643_ = lean_unsigned_to_nat(4u);
v___x_644_ = lean_nat_dec_lt(v___x_642_, v___x_643_);
lean_dec(v___x_642_);
v___y_634_ = v___x_644_;
goto v___jp_633_;
}
else
{
v___y_634_ = v___x_641_;
goto v___jp_633_;
}
v___jp_633_:
{
if (v___y_634_ == 0)
{
lean_object* v_ks_635_; lean_object* v_vs_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_ks_635_ = lean_ctor_get(v_newNode_632_, 0);
lean_inc_ref(v_ks_635_);
v_vs_636_ = lean_ctor_get(v_newNode_632_, 1);
lean_inc_ref(v_vs_636_);
lean_dec_ref(v_newNode_632_);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
v___x_639_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_x_576_, v_ks_635_, v_vs_636_, v___x_637_, v___x_638_);
lean_dec_ref(v_vs_636_);
lean_dec_ref(v_ks_635_);
return v___x_639_;
}
else
{
return v_newNode_632_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(size_t v_depth_647_, lean_object* v_keys_648_, lean_object* v_vals_649_, lean_object* v_i_650_, lean_object* v_entries_651_){
_start:
{
lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_652_ = lean_array_get_size(v_keys_648_);
v___x_653_ = lean_nat_dec_lt(v_i_650_, v___x_652_);
if (v___x_653_ == 0)
{
lean_dec(v_i_650_);
return v_entries_651_;
}
else
{
lean_object* v_k_654_; lean_object* v_v_655_; uint64_t v___x_656_; size_t v_h_657_; size_t v___x_658_; lean_object* v___x_659_; size_t v___x_660_; size_t v___x_661_; size_t v___x_662_; size_t v_h_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_k_654_ = lean_array_fget_borrowed(v_keys_648_, v_i_650_);
v_v_655_ = lean_array_fget_borrowed(v_vals_649_, v_i_650_);
v___x_656_ = lean_string_hash(v_k_654_);
v_h_657_ = lean_uint64_to_usize(v___x_656_);
v___x_658_ = ((size_t)5ULL);
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = ((size_t)1ULL);
v___x_661_ = lean_usize_sub(v_depth_647_, v___x_660_);
v___x_662_ = lean_usize_mul(v___x_658_, v___x_661_);
v_h_663_ = lean_usize_shift_right(v_h_657_, v___x_662_);
v___x_664_ = lean_nat_add(v_i_650_, v___x_659_);
lean_dec(v_i_650_);
lean_inc(v_v_655_);
lean_inc(v_k_654_);
v___x_665_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_entries_651_, v_h_663_, v_depth_647_, v_k_654_, v_v_655_);
v_i_650_ = v___x_664_;
v_entries_651_ = v___x_665_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_depth_667_, lean_object* v_keys_668_, lean_object* v_vals_669_, lean_object* v_i_670_, lean_object* v_entries_671_){
_start:
{
size_t v_depth_boxed_672_; lean_object* v_res_673_; 
v_depth_boxed_672_ = lean_unbox_usize(v_depth_667_);
lean_dec(v_depth_667_);
v_res_673_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_depth_boxed_672_, v_keys_668_, v_vals_669_, v_i_670_, v_entries_671_);
lean_dec_ref(v_vals_669_);
lean_dec_ref(v_keys_668_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_x_674_, lean_object* v_x_675_, lean_object* v_x_676_, lean_object* v_x_677_, lean_object* v_x_678_){
_start:
{
size_t v_x_817__boxed_679_; size_t v_x_818__boxed_680_; lean_object* v_res_681_; 
v_x_817__boxed_679_ = lean_unbox_usize(v_x_675_);
lean_dec(v_x_675_);
v_x_818__boxed_680_ = lean_unbox_usize(v_x_676_);
lean_dec(v_x_676_);
v_res_681_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_674_, v_x_817__boxed_679_, v_x_818__boxed_680_, v_x_677_, v_x_678_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* v_x_682_, lean_object* v_x_683_, lean_object* v_x_684_){
_start:
{
uint64_t v___x_685_; size_t v___x_686_; size_t v___x_687_; lean_object* v___x_688_; 
v___x_685_ = lean_string_hash(v_x_683_);
v___x_686_ = lean_uint64_to_usize(v___x_685_);
v___x_687_ = ((size_t)1ULL);
v___x_688_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_682_, v___x_686_, v___x_687_, v_x_683_, v_x_684_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_691_){
_start:
{
lean_object* v___x_692_; 
lean_inc(v_params_691_);
v___x_692_ = l_Lean_Lsp_instFromJsonRpcCallParams_fromJson(v_params_691_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_708_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_708_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_708_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_708_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
uint8_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_697_ = 3;
v___x_698_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_699_ = l_Lean_Json_compress(v_params_691_);
v___x_700_ = lean_string_append(v___x_698_, v___x_699_);
lean_dec_ref(v___x_699_);
v___x_701_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__1));
v___x_702_ = lean_string_append(v___x_700_, v___x_701_);
v___x_703_ = lean_string_append(v___x_702_, v_a_693_);
lean_dec(v_a_693_);
v___x_704_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set_uint8(v___x_704_, sizeof(void*)*1, v___x_697_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_704_);
v___x_706_ = v___x_695_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec(v_params_691_);
v_a_709_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_692_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_692_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_717_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0(v_params_717_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
lean_ctor_set_tag(v___x_722_, 1);
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
v_a_728_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_719_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_719_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set_tag(v___x_730_, 0);
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_736_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_739_, lean_object* v___f_740_, lean_object* v_j_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_741_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_746_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref(v___x_744_);
lean_inc_ref(v___y_742_);
v___x_746_ = lean_apply_3(v_handler_739_, v_a_745_, v___y_742_, lean_box(0));
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_755_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_755_ == 0)
{
v___x_749_ = v___x_746_;
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_746_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_751_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_740_, v_a_747_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_751_);
v___x_753_ = v___x_749_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec_ref(v___f_740_);
v_a_756_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_746_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_746_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec_ref(v___f_740_);
lean_dec_ref(v_handler_739_);
v_a_764_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_744_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_744_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_772_, lean_object* v___f_773_, lean_object* v_j_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2(v_handler_772_, v___f_773_, v_j_774_, v___y_775_);
lean_dec_ref(v___y_775_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0(v_j_778_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_797_; 
v_a_788_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_797_ == 0)
{
v___x_790_ = v___x_779_;
v_isShared_791_ = v_isSharedCheck_797_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_779_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_797_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v_toTextDocumentPositionParams_792_; lean_object* v_textDocument_793_; lean_object* v___x_795_; 
v_toTextDocumentPositionParams_792_ = lean_ctor_get(v_a_788_, 0);
lean_inc_ref(v_toTextDocumentPositionParams_792_);
lean_dec(v_a_788_);
v_textDocument_793_ = lean_ctor_get(v_toTextDocumentPositionParams_792_, 0);
lean_inc_ref(v_textDocument_793_);
lean_dec_ref(v_toTextDocumentPositionParams_792_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v_textDocument_793_);
v___x_795_ = v___x_790_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_textDocument_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_keys_798_, lean_object* v_i_799_, lean_object* v_k_800_){
_start:
{
lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_801_ = lean_array_get_size(v_keys_798_);
v___x_802_ = lean_nat_dec_lt(v_i_799_, v___x_801_);
if (v___x_802_ == 0)
{
lean_dec(v_i_799_);
return v___x_802_;
}
else
{
lean_object* v_k_x27_803_; uint8_t v___x_804_; 
v_k_x27_803_ = lean_array_fget_borrowed(v_keys_798_, v_i_799_);
v___x_804_ = lean_string_dec_eq(v_k_800_, v_k_x27_803_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = lean_unsigned_to_nat(1u);
v___x_806_ = lean_nat_add(v_i_799_, v___x_805_);
lean_dec(v_i_799_);
v_i_799_ = v___x_806_;
goto _start;
}
else
{
lean_dec(v_i_799_);
return v___x_804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_keys_808_, lean_object* v_i_809_, lean_object* v_k_810_){
_start:
{
uint8_t v_res_811_; lean_object* v_r_812_; 
v_res_811_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(v_keys_808_, v_i_809_, v_k_810_);
lean_dec_ref(v_k_810_);
lean_dec_ref(v_keys_808_);
v_r_812_ = lean_box(v_res_811_);
return v_r_812_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object* v_x_813_, size_t v_x_814_, lean_object* v_x_815_){
_start:
{
if (lean_obj_tag(v_x_813_) == 0)
{
lean_object* v_es_816_; lean_object* v___x_817_; size_t v___x_818_; size_t v___x_819_; size_t v___x_820_; lean_object* v_j_821_; lean_object* v___x_822_; 
v_es_816_ = lean_ctor_get(v_x_813_, 0);
v___x_817_ = lean_box(2);
v___x_818_ = ((size_t)5ULL);
v___x_819_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1);
v___x_820_ = lean_usize_land(v_x_814_, v___x_819_);
v_j_821_ = lean_usize_to_nat(v___x_820_);
v___x_822_ = lean_array_get_borrowed(v___x_817_, v_es_816_, v_j_821_);
lean_dec(v_j_821_);
switch(lean_obj_tag(v___x_822_))
{
case 0:
{
lean_object* v_key_823_; uint8_t v___x_824_; 
v_key_823_ = lean_ctor_get(v___x_822_, 0);
v___x_824_ = lean_string_dec_eq(v_x_815_, v_key_823_);
return v___x_824_;
}
case 1:
{
lean_object* v_node_825_; size_t v___x_826_; 
v_node_825_ = lean_ctor_get(v___x_822_, 0);
v___x_826_ = lean_usize_shift_right(v_x_814_, v___x_818_);
v_x_813_ = v_node_825_;
v_x_814_ = v___x_826_;
goto _start;
}
default: 
{
uint8_t v___x_828_; 
v___x_828_ = 0;
return v___x_828_;
}
}
}
else
{
lean_object* v_ks_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v_ks_829_ = lean_ctor_get(v_x_813_, 0);
v___x_830_ = lean_unsigned_to_nat(0u);
v___x_831_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(v_ks_829_, v___x_830_, v_x_815_);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_x_832_, lean_object* v_x_833_, lean_object* v_x_834_){
_start:
{
size_t v_x_1197__boxed_835_; uint8_t v_res_836_; lean_object* v_r_837_; 
v_x_1197__boxed_835_ = lean_unbox_usize(v_x_833_);
lean_dec(v_x_833_);
v_res_836_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_832_, v_x_1197__boxed_835_, v_x_834_);
lean_dec_ref(v_x_834_);
lean_dec_ref(v_x_832_);
v_r_837_ = lean_box(v_res_836_);
return v_r_837_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
uint64_t v___x_840_; size_t v___x_841_; uint8_t v___x_842_; 
v___x_840_ = lean_string_hash(v_x_839_);
v___x_841_ = lean_uint64_to_usize(v___x_840_);
v___x_842_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_838_, v___x_841_, v_x_839_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_x_843_, lean_object* v_x_844_){
_start:
{
uint8_t v_res_845_; lean_object* v_r_846_; 
v_res_845_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_843_, v_x_844_);
lean_dec_ref(v_x_844_);
lean_dec_ref(v_x_843_);
v_r_846_ = lean_box(v_res_845_);
return v_r_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0(lean_object* v_method_851_, lean_object* v_handler_852_, lean_object* v_serialize_x3f_853_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_initializing();
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_890_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_890_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_890_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_890_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
uint8_t v___x_860_; 
v___x_860_ = lean_unbox(v_a_856_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_867_; 
lean_dec(v_a_856_);
lean_dec(v_serialize_x3f_853_);
lean_dec_ref(v_handler_852_);
v___x_861_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__0));
v___x_862_ = lean_string_append(v___x_861_, v_method_851_);
lean_dec_ref(v_method_851_);
v___x_863_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__1));
v___x_864_ = lean_string_append(v___x_862_, v___x_863_);
v___x_865_ = lean_mk_io_user_error(v___x_864_);
if (v_isShared_859_ == 0)
{
lean_ctor_set_tag(v___x_858_, 1);
lean_ctor_set(v___x_858_, 0, v___x_865_);
v___x_867_ = v___x_858_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
else
{
lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_869_ = l_Lean_Server_requestHandlers;
v___x_870_ = lean_st_ref_get(v___x_869_);
v___x_871_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_870_, v_method_851_);
lean_dec(v___x_870_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; lean_object* v___f_873_; lean_object* v___f_874_; lean_object* v___f_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_872_ = lean_st_ref_take(v___x_869_);
v___f_873_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__2));
v___f_874_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_874_, 0, v_serialize_x3f_853_);
lean_closure_set(v___f_874_, 1, v_a_856_);
v___f_875_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_875_, 0, v_handler_852_);
lean_closure_set(v___f_875_, 1, v___f_874_);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v___f_873_);
lean_ctor_set(v___x_876_, 1, v___f_875_);
v___x_877_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_872_, v_method_851_, v___x_876_);
v___x_878_ = lean_st_ref_set(v___x_869_, v___x_877_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_878_);
v___x_880_ = v___x_858_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
else
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_888_; 
lean_dec(v_a_856_);
lean_dec(v_serialize_x3f_853_);
lean_dec_ref(v_handler_852_);
v___x_882_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__0));
v___x_883_ = lean_string_append(v___x_882_, v_method_851_);
lean_dec_ref(v_method_851_);
v___x_884_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__3));
v___x_885_ = lean_string_append(v___x_883_, v___x_884_);
v___x_886_ = lean_mk_io_user_error(v___x_885_);
if (v_isShared_859_ == 0)
{
lean_ctor_set_tag(v___x_858_, 1);
lean_ctor_set(v___x_858_, 0, v___x_886_);
v___x_888_ = v___x_858_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec(v_serialize_x3f_853_);
lean_dec_ref(v_handler_852_);
lean_dec_ref(v_method_851_);
v_a_891_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_855_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_855_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_899_, lean_object* v_handler_900_, lean_object* v_serialize_x3f_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0(v_method_899_, v_handler_900_, v_serialize_x3f_901_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_907_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_));
v___x_908_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_));
v___x_909_ = lean_box(0);
v___x_910_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0(v___x_907_, v___x_908_, v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2____boxed(lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_();
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_913_, lean_object* v_a_914_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_913_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1(v_params_917_, v_a_918_);
lean_dec_ref(v_a_918_);
return v_res_920_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_921_, lean_object* v_x_922_, lean_object* v_x_923_){
_start:
{
uint8_t v___x_924_; 
v___x_924_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_922_, v_x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_925_, lean_object* v_x_926_, lean_object* v_x_927_){
_start:
{
uint8_t v_res_928_; lean_object* v_r_929_; 
v_res_928_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_925_, v_x_926_, v_x_927_);
lean_dec_ref(v_x_927_);
lean_dec_ref(v_x_926_);
v_r_929_ = lean_box(v_res_928_);
return v_r_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_00_u03b2_930_, lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v_x_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_931_, v_x_932_, v_x_933_);
return v___x_934_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object* v_00_u03b2_935_, lean_object* v_x_936_, size_t v_x_937_, lean_object* v_x_938_){
_start:
{
uint8_t v___x_939_; 
v___x_939_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_936_, v_x_937_, v_x_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_940_, lean_object* v_x_941_, lean_object* v_x_942_, lean_object* v_x_943_){
_start:
{
size_t v_x_1394__boxed_944_; uint8_t v_res_945_; lean_object* v_r_946_; 
v_x_1394__boxed_944_ = lean_unbox_usize(v_x_942_);
lean_dec(v_x_942_);
v_res_945_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_00_u03b2_940_, v_x_941_, v_x_1394__boxed_944_, v_x_943_);
lean_dec_ref(v_x_943_);
lean_dec_ref(v_x_941_);
v_r_946_ = lean_box(v_res_945_);
return v_r_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* v_00_u03b2_947_, lean_object* v_x_948_, size_t v_x_949_, size_t v_x_950_, lean_object* v_x_951_, lean_object* v_x_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_948_, v_x_949_, v_x_950_, v_x_951_, v_x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_954_, lean_object* v_x_955_, lean_object* v_x_956_, lean_object* v_x_957_, lean_object* v_x_958_, lean_object* v_x_959_){
_start:
{
size_t v_x_1405__boxed_960_; size_t v_x_1406__boxed_961_; lean_object* v_res_962_; 
v_x_1405__boxed_960_ = lean_unbox_usize(v_x_956_);
lean_dec(v_x_956_);
v_x_1406__boxed_961_ = lean_unbox_usize(v_x_957_);
lean_dec(v_x_957_);
v_res_962_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_954_, v_x_955_, v_x_1405__boxed_960_, v_x_1406__boxed_961_, v_x_958_, v_x_959_);
return v_res_962_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_963_, lean_object* v_keys_964_, lean_object* v_vals_965_, lean_object* v_heq_966_, lean_object* v_i_967_, lean_object* v_k_968_){
_start:
{
uint8_t v___x_969_; 
v___x_969_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(v_keys_964_, v_i_967_, v_k_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_970_, lean_object* v_keys_971_, lean_object* v_vals_972_, lean_object* v_heq_973_, lean_object* v_i_974_, lean_object* v_k_975_){
_start:
{
uint8_t v_res_976_; lean_object* v_r_977_; 
v_res_976_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4(v_00_u03b2_970_, v_keys_971_, v_vals_972_, v_heq_973_, v_i_974_, v_k_975_);
lean_dec_ref(v_k_975_);
lean_dec_ref(v_vals_972_);
lean_dec_ref(v_keys_971_);
v_r_977_ = lean_box(v_res_976_);
return v_r_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_978_, lean_object* v_n_979_, lean_object* v_k_980_, lean_object* v_v_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7___redArg(v_n_979_, v_k_980_, v_v_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_983_, size_t v_depth_984_, lean_object* v_keys_985_, lean_object* v_vals_986_, lean_object* v_heq_987_, lean_object* v_i_988_, lean_object* v_entries_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_depth_984_, v_keys_985_, v_vals_986_, v_i_988_, v_entries_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_991_, lean_object* v_depth_992_, lean_object* v_keys_993_, lean_object* v_vals_994_, lean_object* v_heq_995_, lean_object* v_i_996_, lean_object* v_entries_997_){
_start:
{
size_t v_depth_boxed_998_; lean_object* v_res_999_; 
v_depth_boxed_998_ = lean_unbox_usize(v_depth_992_);
lean_dec(v_depth_992_);
v_res_999_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(v_00_u03b2_991_, v_depth_boxed_998_, v_keys_993_, v_vals_994_, v_heq_995_, v_i_996_, v_entries_997_);
lean_dec_ref(v_vals_994_);
lean_dec_ref(v_keys_993_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8(lean_object* v_00_u03b2_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8___redArg(v_x_1001_, v_x_1002_, v_x_1003_, v_x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_wrapRpcProcedure___redArg___lam__0(uint64_t v_x_1006_, uint64_t v_y_1007_){
_start:
{
uint8_t v___x_1008_; 
v___x_1008_ = lean_uint64_dec_lt(v_x_1006_, v_y_1007_);
if (v___x_1008_ == 0)
{
uint8_t v___x_1009_; 
v___x_1009_ = lean_uint64_dec_eq(v_x_1006_, v_y_1007_);
if (v___x_1009_ == 0)
{
uint8_t v___x_1010_; 
v___x_1010_ = 2;
return v___x_1010_;
}
else
{
uint8_t v___x_1011_; 
v___x_1011_ = 1;
return v___x_1011_;
}
}
else
{
uint8_t v___x_1012_; 
v___x_1012_ = 0;
return v___x_1012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__0___boxed(lean_object* v_x_1013_, lean_object* v_y_1014_){
_start:
{
uint64_t v_x_boxed_1015_; uint64_t v_y_boxed_1016_; uint8_t v_res_1017_; lean_object* v_r_1018_; 
v_x_boxed_1015_ = lean_unbox_uint64(v_x_1013_);
lean_dec_ref(v_x_1013_);
v_y_boxed_1016_ = lean_unbox_uint64(v_y_1014_);
lean_dec_ref(v_y_1014_);
v_res_1017_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__0(v_x_boxed_1015_, v_y_boxed_1016_);
v_r_1018_ = lean_box(v_res_1017_);
return v_r_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__1(lean_object* v_expireTime_1019_, lean_object* v_x_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v_x_1020_);
lean_ctor_set(v___x_1021_, 1, v_expireTime_1019_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__2(lean_object* v_val_1023_, lean_object* v_inst_1024_, lean_object* v_x_1025_, lean_object* v___y_1026_){
_start:
{
if (lean_obj_tag(v_x_1025_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec_ref(v_inst_1024_);
v_a_1028_ = lean_ctor_get(v_x_1025_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_x_1025_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v_x_1025_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v_x_1025_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set_tag(v___x_1030_, 1);
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1054_; 
v_a_1036_ = lean_ctor_get(v_x_1025_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_x_1025_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1038_ = v_x_1025_;
v_isShared_1039_ = v_isSharedCheck_1054_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v_x_1025_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1054_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v_rpcEncode_1041_; lean_object* v_objects_1042_; lean_object* v_expireTime_1043_; lean_object* v___f_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v_fst_1048_; lean_object* v_snd_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1040_ = lean_st_ref_take(v_val_1023_);
v_rpcEncode_1041_ = lean_ctor_get(v_inst_1024_, 0);
lean_inc_ref(v_rpcEncode_1041_);
lean_dec_ref(v_inst_1024_);
v_objects_1042_ = lean_ctor_get(v___x_1040_, 0);
lean_inc_ref(v_objects_1042_);
v_expireTime_1043_ = lean_ctor_get(v___x_1040_, 1);
lean_inc(v_expireTime_1043_);
lean_dec(v___x_1040_);
v___f_1044_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1044_, 0, v_expireTime_1043_);
v___x_1045_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__2___closed__0));
v___x_1046_ = lean_apply_2(v_rpcEncode_1041_, v_a_1036_, v_objects_1042_);
v___x_1047_ = l_Prod_map___redArg(v___x_1045_, v___f_1044_, v___x_1046_);
v_fst_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_fst_1048_);
v_snd_1049_ = lean_ctor_get(v___x_1047_, 1);
lean_inc(v_snd_1049_);
lean_dec_ref(v___x_1047_);
v___x_1050_ = lean_st_ref_set(v_val_1023_, v_snd_1049_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 0);
lean_ctor_set(v___x_1038_, 0, v_fst_1048_);
v___x_1052_ = v___x_1038_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_fst_1048_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__2___boxed(lean_object* v_val_1055_, lean_object* v_inst_1056_, lean_object* v_x_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__2(v_val_1055_, v_inst_1056_, v_x_1057_, v___y_1058_);
lean_dec_ref(v___y_1058_);
lean_dec(v_val_1055_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__3(lean_object* v___f_1068_, lean_object* v_inst_1069_, lean_object* v_method_1070_, lean_object* v_handler_1071_, lean_object* v_inst_1072_, uint64_t v_seshId_1073_, lean_object* v_j_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_rpcSessions_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v_rpcSessions_1077_ = lean_ctor_get(v___y_1075_, 0);
v___x_1078_ = lean_box_uint64(v_seshId_1073_);
lean_inc(v_rpcSessions_1077_);
v___x_1079_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_1068_, v_rpcSessions_1077_, v___x_1078_);
if (lean_obj_tag(v___x_1079_) == 1)
{
lean_object* v_val_1080_; lean_object* v___x_1081_; lean_object* v_rpcDecode_1082_; lean_object* v_objects_1083_; lean_object* v___x_1084_; 
v_val_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_val_1080_);
lean_dec_ref(v___x_1079_);
v___x_1081_ = lean_st_ref_get(v_val_1080_);
v_rpcDecode_1082_ = lean_ctor_get(v_inst_1069_, 1);
lean_inc_ref(v_rpcDecode_1082_);
lean_dec_ref(v_inst_1069_);
v_objects_1083_ = lean_ctor_get(v___x_1081_, 0);
lean_inc_ref(v_objects_1083_);
lean_dec(v___x_1081_);
lean_inc(v_j_1074_);
v___x_1084_ = lean_apply_2(v_rpcDecode_1082_, v_j_1074_, v_objects_1083_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1105_; 
lean_dec(v_val_1080_);
lean_dec_ref(v_inst_1072_);
lean_dec_ref(v_handler_1071_);
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1105_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1105_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
uint8_t v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1089_ = 3;
v___x_1090_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__0));
v___x_1091_ = 1;
v___x_1092_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_1070_, v___x_1091_);
v___x_1093_ = lean_string_append(v___x_1090_, v___x_1092_);
lean_dec_ref(v___x_1092_);
v___x_1094_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__1));
v___x_1095_ = lean_string_append(v___x_1093_, v___x_1094_);
v___x_1096_ = l_Lean_Json_compress(v_j_1074_);
v___x_1097_ = lean_string_append(v___x_1095_, v___x_1096_);
lean_dec_ref(v___x_1096_);
v___x_1098_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__2));
v___x_1099_ = lean_string_append(v___x_1097_, v___x_1098_);
v___x_1100_ = lean_string_append(v___x_1099_, v_a_1085_);
lean_dec(v_a_1085_);
v___x_1101_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
lean_ctor_set_uint8(v___x_1101_, sizeof(void*)*1, v___x_1089_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set_tag(v___x_1087_, 1);
lean_ctor_set(v___x_1087_, 0, v___x_1101_);
v___x_1103_ = v___x_1087_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1107_; 
lean_dec(v_j_1074_);
lean_dec(v_method_1070_);
v_a_1106_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1106_);
lean_dec_ref(v___x_1084_);
lean_inc_ref(v___y_1075_);
v___x_1107_ = lean_apply_3(v_handler_1071_, v_a_1106_, v___y_1075_, lean_box(0));
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___f_1109_; lean_object* v___x_1110_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
lean_dec_ref(v___x_1107_);
v___f_1109_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_1109_, 0, v_val_1080_);
lean_closure_set(v___f_1109_, 1, v_inst_1072_);
v___x_1110_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_a_1108_, v___f_1109_, v___y_1075_);
return v___x_1110_;
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec(v_val_1080_);
lean_dec_ref(v_inst_1072_);
v_a_1111_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1107_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1107_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
else
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_dec(v___x_1079_);
lean_dec(v_j_1074_);
lean_dec_ref(v_inst_1072_);
lean_dec_ref(v_handler_1071_);
lean_dec(v_method_1070_);
lean_dec_ref(v_inst_1069_);
v___x_1119_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__4));
v___x_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
return v___x_1120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__3___boxed(lean_object* v___f_1121_, lean_object* v_inst_1122_, lean_object* v_method_1123_, lean_object* v_handler_1124_, lean_object* v_inst_1125_, lean_object* v_seshId_1126_, lean_object* v_j_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
uint64_t v_seshId_boxed_1130_; lean_object* v_res_1131_; 
v_seshId_boxed_1130_ = lean_unbox_uint64(v_seshId_1126_);
lean_dec_ref(v_seshId_1126_);
v_res_1131_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__3(v___f_1121_, v_inst_1122_, v_method_1123_, v_handler_1124_, v_inst_1125_, v_seshId_boxed_1130_, v_j_1127_, v___y_1128_);
lean_dec_ref(v___y_1128_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg(lean_object* v_method_1133_, lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_handler_1136_){
_start:
{
lean_object* v___f_1137_; lean_object* v___f_1138_; 
v___f_1137_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___closed__0));
v___f_1138_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___boxed), 9, 5);
lean_closure_set(v___f_1138_, 0, v___f_1137_);
lean_closure_set(v___f_1138_, 1, v_inst_1134_);
lean_closure_set(v___f_1138_, 2, v_method_1133_);
lean_closure_set(v___f_1138_, 3, v_handler_1136_);
lean_closure_set(v___f_1138_, 4, v_inst_1135_);
return v___f_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure(lean_object* v_method_1139_, lean_object* v_paramType_1140_, lean_object* v_respType_1141_, lean_object* v_inst_1142_, lean_object* v_inst_1143_, lean_object* v_handler_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_Server_wrapRpcProcedure___redArg(v_method_1139_, v_inst_1142_, v_inst_1143_, v_handler_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg(lean_object* v_method_1152_, lean_object* v_inst_1153_, lean_object* v_inst_1154_, lean_object* v_handler_1155_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_initializing();
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1193_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1193_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1193_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; uint8_t v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v_errMsg_1167_; uint8_t v___x_1168_; 
v___x_1162_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__0));
v___x_1163_ = 1;
lean_inc(v_method_1152_);
v___x_1164_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_1152_, v___x_1163_);
v___x_1165_ = lean_string_append(v___x_1162_, v___x_1164_);
lean_dec_ref(v___x_1164_);
v___x_1166_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__1));
v_errMsg_1167_ = lean_string_append(v___x_1165_, v___x_1166_);
v___x_1168_ = lean_unbox(v_a_1158_);
lean_dec(v_a_1158_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
lean_dec_ref(v_handler_1155_);
lean_dec_ref(v_inst_1154_);
lean_dec_ref(v_inst_1153_);
lean_dec(v_method_1152_);
v___x_1169_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__2));
v___x_1170_ = lean_string_append(v_errMsg_1167_, v___x_1169_);
v___x_1171_ = lean_mk_io_user_error(v___x_1170_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set_tag(v___x_1160_, 1);
lean_ctor_set(v___x_1160_, 0, v___x_1171_);
v___x_1173_ = v___x_1160_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1175_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_1176_ = lean_st_ref_get(v___x_1175_);
v___x_1177_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__3));
v___x_1178_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__4));
lean_inc(v_method_1152_);
v___x_1179_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1177_, v___x_1178_, v___x_1176_, v_method_1152_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; 
lean_dec_ref(v_errMsg_1167_);
v___x_1180_ = lean_st_ref_take(v___x_1175_);
lean_inc(v_method_1152_);
v___x_1181_ = l_Lean_Server_wrapRpcProcedure___redArg(v_method_1152_, v_inst_1153_, v_inst_1154_, v_handler_1155_);
v___x_1182_ = l_Lean_PersistentHashMap_insert___redArg(v___x_1177_, v___x_1178_, v___x_1180_, v_method_1152_, v___x_1181_);
v___x_1183_ = lean_st_ref_set(v___x_1175_, v___x_1182_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1183_);
v___x_1185_ = v___x_1160_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
else
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1191_; 
lean_dec_ref(v_handler_1155_);
lean_dec_ref(v_inst_1154_);
lean_dec_ref(v_inst_1153_);
lean_dec(v_method_1152_);
v___x_1187_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__5));
v___x_1188_ = lean_string_append(v_errMsg_1167_, v___x_1187_);
v___x_1189_ = lean_mk_io_user_error(v___x_1188_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set_tag(v___x_1160_, 1);
lean_ctor_set(v___x_1160_, 0, v___x_1189_);
v___x_1191_ = v___x_1160_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec_ref(v_handler_1155_);
lean_dec_ref(v_inst_1154_);
lean_dec_ref(v_inst_1153_);
lean_dec(v_method_1152_);
v_a_1194_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1157_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1157_);
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
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg___boxed(lean_object* v_method_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_handler_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_Server_registerBuiltinRpcProcedure___redArg(v_method_1202_, v_inst_1203_, v_inst_1204_, v_handler_1205_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure(lean_object* v_method_1208_, lean_object* v_paramType_1209_, lean_object* v_respType_1210_, lean_object* v_inst_1211_, lean_object* v_inst_1212_, lean_object* v_handler_1213_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_Server_registerBuiltinRpcProcedure___redArg(v_method_1208_, v_inst_1211_, v_inst_1212_, v_handler_1213_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___boxed(lean_object* v_method_1216_, lean_object* v_paramType_1217_, lean_object* v_respType_1218_, lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v_handler_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_Server_registerBuiltinRpcProcedure(v_method_1216_, v_paramType_1217_, v_respType_1218_, v_inst_1219_, v_inst_1220_, v_handler_1221_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(lean_object* v_e_1224_, lean_object* v___y_1225_){
_start:
{
uint8_t v___x_1227_; 
v___x_1227_ = l_Lean_Expr_hasMVar(v_e_1224_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; 
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v_e_1224_);
return v___x_1228_;
}
else
{
lean_object* v___x_1229_; lean_object* v_mctx_1230_; lean_object* v___x_1231_; lean_object* v_fst_1232_; lean_object* v_snd_1233_; lean_object* v___x_1234_; lean_object* v_cache_1235_; lean_object* v_zetaDeltaFVarIds_1236_; lean_object* v_postponed_1237_; lean_object* v_diag_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1247_; 
v___x_1229_ = lean_st_ref_get(v___y_1225_);
v_mctx_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc_ref(v_mctx_1230_);
lean_dec(v___x_1229_);
v___x_1231_ = l_Lean_instantiateMVarsCore(v_mctx_1230_, v_e_1224_);
v_fst_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_fst_1232_);
v_snd_1233_ = lean_ctor_get(v___x_1231_, 1);
lean_inc(v_snd_1233_);
lean_dec_ref(v___x_1231_);
v___x_1234_ = lean_st_ref_take(v___y_1225_);
v_cache_1235_ = lean_ctor_get(v___x_1234_, 1);
v_zetaDeltaFVarIds_1236_ = lean_ctor_get(v___x_1234_, 2);
v_postponed_1237_ = lean_ctor_get(v___x_1234_, 3);
v_diag_1238_ = lean_ctor_get(v___x_1234_, 4);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; 
v_unused_1248_ = lean_ctor_get(v___x_1234_, 0);
lean_dec(v_unused_1248_);
v___x_1240_ = v___x_1234_;
v_isShared_1241_ = v_isSharedCheck_1247_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_diag_1238_);
lean_inc(v_postponed_1237_);
lean_inc(v_zetaDeltaFVarIds_1236_);
lean_inc(v_cache_1235_);
lean_dec(v___x_1234_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1247_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 0, v_snd_1233_);
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_snd_1233_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_cache_1235_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_zetaDeltaFVarIds_1236_);
lean_ctor_set(v_reuseFailAlloc_1246_, 3, v_postponed_1237_);
lean_ctor_set(v_reuseFailAlloc_1246_, 4, v_diag_1238_);
v___x_1243_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_st_ref_set(v___y_1225_, v___x_1243_);
v___x_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1245_, 0, v_fst_1232_);
return v___x_1245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg___boxed(lean_object* v_e_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(v_e_1249_, v___y_1250_);
lean_dec(v___y_1250_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0(lean_object* v_e_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(v_e_1253_, v___y_1257_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___boxed(lean_object* v_e_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0(v_e_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg(lean_object* v_a_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg___boxed(lean_object* v_a_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg(v_a_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1(lean_object* v_00_u03b1_1289_, lean_object* v_a_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___boxed(lean_object* v_00_u03b1_1299_, lean_object* v_a_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1(v_00_u03b1_1299_, v_a_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
return v_res_1308_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1309_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0);
v___x_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
return v___x_1311_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1);
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(lean_object* v_env_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; lean_object* v_nextMacroScope_1318_; lean_object* v_ngen_1319_; lean_object* v_auxDeclNGen_1320_; lean_object* v_traceState_1321_; lean_object* v_messages_1322_; lean_object* v_infoState_1323_; lean_object* v_snapshotTasks_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1335_; 
v___x_1317_ = lean_st_ref_take(v___y_1315_);
v_nextMacroScope_1318_ = lean_ctor_get(v___x_1317_, 1);
v_ngen_1319_ = lean_ctor_get(v___x_1317_, 2);
v_auxDeclNGen_1320_ = lean_ctor_get(v___x_1317_, 3);
v_traceState_1321_ = lean_ctor_get(v___x_1317_, 4);
v_messages_1322_ = lean_ctor_get(v___x_1317_, 6);
v_infoState_1323_ = lean_ctor_get(v___x_1317_, 7);
v_snapshotTasks_1324_ = lean_ctor_get(v___x_1317_, 8);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; lean_object* v_unused_1337_; 
v_unused_1336_ = lean_ctor_get(v___x_1317_, 5);
lean_dec(v_unused_1336_);
v_unused_1337_ = lean_ctor_get(v___x_1317_, 0);
lean_dec(v_unused_1337_);
v___x_1326_ = v___x_1317_;
v_isShared_1327_ = v_isSharedCheck_1335_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_snapshotTasks_1324_);
lean_inc(v_infoState_1323_);
lean_inc(v_messages_1322_);
lean_inc(v_traceState_1321_);
lean_inc(v_auxDeclNGen_1320_);
lean_inc(v_ngen_1319_);
lean_inc(v_nextMacroScope_1318_);
lean_dec(v___x_1317_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1335_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1328_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__2);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 5, v___x_1328_);
lean_ctor_set(v___x_1326_, 0, v_env_1314_);
v___x_1330_ = v___x_1326_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_env_1314_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_nextMacroScope_1318_);
lean_ctor_set(v_reuseFailAlloc_1334_, 2, v_ngen_1319_);
lean_ctor_set(v_reuseFailAlloc_1334_, 3, v_auxDeclNGen_1320_);
lean_ctor_set(v_reuseFailAlloc_1334_, 4, v_traceState_1321_);
lean_ctor_set(v_reuseFailAlloc_1334_, 5, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1334_, 6, v_messages_1322_);
lean_ctor_set(v_reuseFailAlloc_1334_, 7, v_infoState_1323_);
lean_ctor_set(v_reuseFailAlloc_1334_, 8, v_snapshotTasks_1324_);
v___x_1330_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1331_ = lean_st_ref_set(v___y_1315_, v___x_1330_);
v___x_1332_ = lean_box(0);
v___x_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
return v___x_1333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___boxed(lean_object* v_env_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(v_env_1338_, v___y_1339_);
lean_dec(v___y_1339_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2(lean_object* v_env_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(v_env_1342_, v___y_1344_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___boxed(lean_object* v_env_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2(v_env_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
return v_res_1351_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_registerRpcProcedure___lam__0(lean_object* v_x_1352_){
_start:
{
uint8_t v___x_1353_; 
v___x_1353_ = 0;
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__0___boxed(lean_object* v_x_1354_){
_start:
{
uint8_t v_res_1355_; lean_object* v_r_1356_; 
v_res_1355_ = l_Lean_Server_registerRpcProcedure___lam__0(v_x_1354_);
lean_dec(v_x_1354_);
v_r_1356_ = lean_box(v_res_1355_);
return v_r_1356_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__3));
v___x_1362_ = l_String_toRawSubstring_x27(v___x_1361_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__1(uint8_t v___x_1373_, lean_object* v___x_1374_, lean_object* v___x_1375_, lean_object* v_method_1376_, lean_object* v___x_1377_, uint8_t v___x_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v_ref_1386_; lean_object* v_quotContext_1387_; lean_object* v_currMacroScope_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___y_1405_; lean_object* v___x_1418_; 
v_ref_1386_ = lean_ctor_get(v___y_1383_, 5);
v_quotContext_1387_ = lean_ctor_get(v___y_1383_, 10);
v_currMacroScope_1388_ = lean_ctor_get(v___y_1383_, 11);
v___x_1389_ = l_Lean_SourceInfo_fromRef(v_ref_1386_, v___x_1373_);
v___x_1390_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__0));
v___x_1391_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__1));
v___x_1392_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__2));
lean_inc_ref_n(v___x_1374_, 2);
v___x_1393_ = l_Lean_Name_mkStr4(v___x_1374_, v___x_1390_, v___x_1391_, v___x_1392_);
v___x_1394_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__3));
v___x_1395_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___lam__1___closed__4, &l_Lean_Server_registerRpcProcedure___lam__1___closed__4_once, _init_l_Lean_Server_registerRpcProcedure___lam__1___closed__4);
v___x_1396_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__5));
lean_inc(v_currMacroScope_1388_);
lean_inc(v_quotContext_1387_);
v___x_1397_ = l_Lean_addMacroScope(v_quotContext_1387_, v___x_1396_, v_currMacroScope_1388_);
v___x_1398_ = l_Lean_Name_mkStr3(v___x_1374_, v___x_1375_, v___x_1394_);
v___x_1399_ = lean_box(0);
v___x_1400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1398_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
v___x_1401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
lean_ctor_set(v___x_1401_, 1, v___x_1399_);
lean_inc(v___x_1389_);
v___x_1402_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1389_);
lean_ctor_set(v___x_1402_, 1, v___x_1395_);
lean_ctor_set(v___x_1402_, 2, v___x_1397_);
lean_ctor_set(v___x_1402_, 3, v___x_1401_);
v___x_1403_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__7));
lean_inc(v_method_1376_);
v___x_1418_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_1399_, v_method_1376_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v___x_1419_; 
lean_inc(v_method_1376_);
v___x_1419_ = l_Lean_quoteNameMk(v_method_1376_);
v___y_1405_ = v___x_1419_;
goto v___jp_1404_;
}
else
{
lean_object* v_val_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v_val_1420_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_val_1420_);
lean_dec_ref(v___x_1418_);
v___x_1421_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__10));
lean_inc_ref(v___x_1374_);
v___x_1422_ = l_Lean_Name_mkStr4(v___x_1374_, v___x_1390_, v___x_1391_, v___x_1421_);
v___x_1423_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__11));
v___x_1424_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__12));
v___x_1425_ = lean_string_intercalate(v___x_1424_, v_val_1420_);
v___x_1426_ = lean_string_append(v___x_1423_, v___x_1425_);
lean_dec_ref(v___x_1425_);
v___x_1427_ = lean_box(2);
v___x_1428_ = l_Lean_Syntax_mkNameLit(v___x_1426_, v___x_1427_);
v___x_1429_ = lean_unsigned_to_nat(1u);
v___x_1430_ = lean_mk_empty_array_with_capacity(v___x_1429_);
v___x_1431_ = lean_array_push(v___x_1430_, v___x_1428_);
v___x_1432_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1427_);
lean_ctor_set(v___x_1432_, 1, v___x_1422_);
lean_ctor_set(v___x_1432_, 2, v___x_1431_);
v___y_1405_ = v___x_1432_;
goto v___jp_1404_;
}
v___jp_1404_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1406_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__8));
v___x_1407_ = l_Lean_Name_mkStr4(v___x_1374_, v___x_1390_, v___x_1391_, v___x_1406_);
v___x_1408_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__9));
lean_inc_n(v___x_1389_, 3);
v___x_1409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1389_);
lean_ctor_set(v___x_1409_, 1, v___x_1408_);
v___x_1410_ = l_Lean_Syntax_node1(v___x_1389_, v___x_1407_, v___x_1409_);
v___x_1411_ = lean_mk_syntax_ident(v_method_1376_);
lean_inc(v___x_1410_);
v___x_1412_ = l_Lean_Syntax_node4(v___x_1389_, v___x_1403_, v___y_1405_, v___x_1410_, v___x_1410_, v___x_1411_);
v___x_1413_ = l_Lean_Syntax_node2(v___x_1389_, v___x_1393_, v___x_1402_, v___x_1412_);
v___x_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1377_);
v___x_1415_ = l_Lean_Elab_Term_elabTerm(v___x_1413_, v___x_1414_, v___x_1378_, v___x_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec_ref(v___y_1383_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1417_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref(v___x_1415_);
v___x_1417_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(v_a_1416_, v___y_1382_);
return v___x_1417_;
}
else
{
return v___x_1415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__1___boxed(lean_object* v___x_1433_, lean_object* v___x_1434_, lean_object* v___x_1435_, lean_object* v_method_1436_, lean_object* v___x_1437_, lean_object* v___x_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
uint8_t v___x_6265__boxed_1446_; uint8_t v___x_6269__boxed_1447_; lean_object* v_res_1448_; 
v___x_6265__boxed_1446_ = lean_unbox(v___x_1433_);
v___x_6269__boxed_1447_ = lean_unbox(v___x_1438_);
v_res_1448_ = l_Lean_Server_registerRpcProcedure___lam__1(v___x_6265__boxed_1446_, v___x_1434_, v___x_1435_, v_method_1436_, v___x_1437_, v___x_6269__boxed_1447_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
return v_res_1448_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1449_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0);
v___x_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
return v___x_1451_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1452_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1);
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
lean_ctor_set(v___x_1454_, 1, v___x_1453_);
lean_ctor_set(v___x_1454_, 2, v___x_1453_);
lean_ctor_set(v___x_1454_, 3, v___x_1453_);
lean_ctor_set(v___x_1454_, 4, v___x_1452_);
lean_ctor_set(v___x_1454_, 5, v___x_1452_);
lean_ctor_set(v___x_1454_, 6, v___x_1452_);
lean_ctor_set(v___x_1454_, 7, v___x_1452_);
lean_ctor_set(v___x_1454_, 8, v___x_1452_);
lean_ctor_set(v___x_1454_, 9, v___x_1452_);
return v___x_1454_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = lean_unsigned_to_nat(32u);
v___x_1456_ = lean_mk_empty_array_with_capacity(v___x_1455_);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
return v___x_1457_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4(void){
_start:
{
size_t v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1458_ = ((size_t)5ULL);
v___x_1459_ = lean_unsigned_to_nat(0u);
v___x_1460_ = lean_unsigned_to_nat(32u);
v___x_1461_ = lean_mk_empty_array_with_capacity(v___x_1460_);
v___x_1462_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3);
v___x_1463_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
lean_ctor_set(v___x_1463_, 1, v___x_1461_);
lean_ctor_set(v___x_1463_, 2, v___x_1459_);
lean_ctor_set(v___x_1463_, 3, v___x_1459_);
lean_ctor_set_usize(v___x_1463_, 4, v___x_1458_);
return v___x_1463_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__5(void){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1464_ = lean_box(1);
v___x_1465_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4);
v___x_1466_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1);
v___x_1467_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
lean_ctor_set(v___x_1467_, 1, v___x_1465_);
lean_ctor_set(v___x_1467_, 2, v___x_1464_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3(lean_object* v_msgData_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v___x_1472_; lean_object* v_env_1473_; lean_object* v_options_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1472_ = lean_st_ref_get(v___y_1470_);
v_env_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc_ref(v_env_1473_);
lean_dec(v___x_1472_);
v_options_1474_ = lean_ctor_get(v___y_1469_, 2);
v___x_1475_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2);
v___x_1476_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__5);
lean_inc_ref(v_options_1474_);
v___x_1477_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1477_, 0, v_env_1473_);
lean_ctor_set(v___x_1477_, 1, v___x_1475_);
lean_ctor_set(v___x_1477_, 2, v___x_1476_);
lean_ctor_set(v___x_1477_, 3, v_options_1474_);
v___x_1478_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
lean_ctor_set(v___x_1478_, 1, v_msgData_1468_);
v___x_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___boxed(lean_object* v_msgData_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3(v_msgData_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(lean_object* v_msg_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_ref_1489_; lean_object* v___x_1490_; lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1499_; 
v_ref_1489_ = lean_ctor_get(v___y_1486_, 5);
v___x_1490_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3(v_msg_1485_, v___y_1486_, v___y_1487_);
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1493_ = v___x_1490_;
v_isShared_1494_ = v_isSharedCheck_1499_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1490_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1499_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; lean_object* v___x_1497_; 
lean_inc(v_ref_1489_);
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v_ref_1489_);
lean_ctor_set(v___x_1495_, 1, v_a_1491_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set_tag(v___x_1493_, 1);
lean_ctor_set(v___x_1493_, 0, v___x_1495_);
v___x_1497_ = v___x_1493_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg___boxed(lean_object* v_msg_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v_msg_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
return v_res_1504_;
}
}
static uint64_t _init_l_Lean_Server_registerRpcProcedure___closed__4(void){
_start:
{
lean_object* v___x_1522_; uint64_t v___x_1523_; 
v___x_1522_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__3));
v___x_1523_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1522_);
return v___x_1523_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__5(void){
_start:
{
uint64_t v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1524_ = lean_uint64_once(&l_Lean_Server_registerRpcProcedure___closed__4, &l_Lean_Server_registerRpcProcedure___closed__4_once, _init_l_Lean_Server_registerRpcProcedure___closed__4);
v___x_1525_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__3));
v___x_1526_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set_uint64(v___x_1526_, sizeof(void*)*1, v___x_1524_);
return v___x_1526_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__6(void){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1527_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__7(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__6, &l_Lean_Server_registerRpcProcedure___closed__6_once, _init_l_Lean_Server_registerRpcProcedure___closed__6);
v___x_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
return v___x_1529_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__8(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1530_ = lean_box(1);
v___x_1531_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4);
v___x_1532_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__7, &l_Lean_Server_registerRpcProcedure___closed__7_once, _init_l_Lean_Server_registerRpcProcedure___closed__7);
v___x_1533_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
lean_ctor_set(v___x_1533_, 1, v___x_1531_);
lean_ctor_set(v___x_1533_, 2, v___x_1530_);
return v___x_1533_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__9(void){
_start:
{
uint8_t v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1534_ = 1;
v___x_1535_ = lean_unsigned_to_nat(0u);
v___x_1536_ = lean_box(0);
v___x_1537_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__1));
v___x_1538_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__8, &l_Lean_Server_registerRpcProcedure___closed__8_once, _init_l_Lean_Server_registerRpcProcedure___closed__8);
v___x_1539_ = lean_box(1);
v___x_1540_ = 0;
v___x_1541_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__5, &l_Lean_Server_registerRpcProcedure___closed__5_once, _init_l_Lean_Server_registerRpcProcedure___closed__5);
v___x_1542_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
lean_ctor_set(v___x_1542_, 1, v___x_1539_);
lean_ctor_set(v___x_1542_, 2, v___x_1538_);
lean_ctor_set(v___x_1542_, 3, v___x_1537_);
lean_ctor_set(v___x_1542_, 4, v___x_1536_);
lean_ctor_set(v___x_1542_, 5, v___x_1535_);
lean_ctor_set(v___x_1542_, 6, v___x_1536_);
lean_ctor_set_uint8(v___x_1542_, sizeof(void*)*7, v___x_1540_);
lean_ctor_set_uint8(v___x_1542_, sizeof(void*)*7 + 1, v___x_1540_);
lean_ctor_set_uint8(v___x_1542_, sizeof(void*)*7 + 2, v___x_1540_);
lean_ctor_set_uint8(v___x_1542_, sizeof(void*)*7 + 3, v___x_1534_);
return v___x_1542_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__10(void){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1543_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__7, &l_Lean_Server_registerRpcProcedure___closed__7_once, _init_l_Lean_Server_registerRpcProcedure___closed__7);
v___x_1544_ = lean_unsigned_to_nat(0u);
v___x_1545_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
lean_ctor_set(v___x_1545_, 2, v___x_1544_);
lean_ctor_set(v___x_1545_, 3, v___x_1544_);
lean_ctor_set(v___x_1545_, 4, v___x_1543_);
lean_ctor_set(v___x_1545_, 5, v___x_1543_);
lean_ctor_set(v___x_1545_, 6, v___x_1543_);
lean_ctor_set(v___x_1545_, 7, v___x_1543_);
lean_ctor_set(v___x_1545_, 8, v___x_1543_);
lean_ctor_set(v___x_1545_, 9, v___x_1543_);
return v___x_1545_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__11(void){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__7, &l_Lean_Server_registerRpcProcedure___closed__7_once, _init_l_Lean_Server_registerRpcProcedure___closed__7);
v___x_1547_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
lean_ctor_set(v___x_1547_, 2, v___x_1546_);
lean_ctor_set(v___x_1547_, 3, v___x_1546_);
lean_ctor_set(v___x_1547_, 4, v___x_1546_);
lean_ctor_set(v___x_1547_, 5, v___x_1546_);
return v___x_1547_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__12(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__7, &l_Lean_Server_registerRpcProcedure___closed__7_once, _init_l_Lean_Server_registerRpcProcedure___closed__7);
v___x_1549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
lean_ctor_set(v___x_1549_, 2, v___x_1548_);
lean_ctor_set(v___x_1549_, 3, v___x_1548_);
lean_ctor_set(v___x_1549_, 4, v___x_1548_);
return v___x_1549_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__13(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1550_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__12, &l_Lean_Server_registerRpcProcedure___closed__12_once, _init_l_Lean_Server_registerRpcProcedure___closed__12);
v___x_1551_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4);
v___x_1552_ = lean_box(1);
v___x_1553_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__11, &l_Lean_Server_registerRpcProcedure___closed__11_once, _init_l_Lean_Server_registerRpcProcedure___closed__11);
v___x_1554_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__10, &l_Lean_Server_registerRpcProcedure___closed__10_once, _init_l_Lean_Server_registerRpcProcedure___closed__10);
v___x_1555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
lean_ctor_set(v___x_1555_, 1, v___x_1553_);
lean_ctor_set(v___x_1555_, 2, v___x_1552_);
lean_ctor_set(v___x_1555_, 3, v___x_1551_);
lean_ctor_set(v___x_1555_, 4, v___x_1550_);
return v___x_1555_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__14(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = lean_box(0);
v___x_1557_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1));
v___x_1558_ = l_Lean_mkConst(v___x_1557_, v___x_1556_);
return v___x_1558_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__18(void){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__7, &l_Lean_Server_registerRpcProcedure___closed__7_once, _init_l_Lean_Server_registerRpcProcedure___closed__7);
v___x_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
return v___x_1566_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__20(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__19));
v___x_1569_ = l_Lean_stringToMessageData(v___x_1568_);
return v___x_1569_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__21(void){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__1));
v___x_1571_ = l_Lean_stringToMessageData(v___x_1570_);
return v___x_1571_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__22(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__5));
v___x_1573_ = l_Lean_stringToMessageData(v___x_1572_);
return v___x_1573_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__24(void){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__23));
v___x_1576_ = l_Lean_stringToMessageData(v___x_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure(lean_object* v_method_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v_env_1584_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___y_1664_; lean_object* v___y_1665_; uint8_t v___x_1671_; 
v___x_1581_ = lean_st_ref_get(v_a_1579_);
v___x_1582_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_1583_ = lean_st_ref_get(v___x_1582_);
v_env_1584_ = lean_ctor_get(v___x_1581_, 0);
lean_inc_ref(v_env_1584_);
lean_dec(v___x_1581_);
v___x_1657_ = lean_box(0);
v___x_1658_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__20, &l_Lean_Server_registerRpcProcedure___closed__20_once, _init_l_Lean_Server_registerRpcProcedure___closed__20);
lean_inc(v_method_1577_);
v___x_1659_ = l_Lean_MessageData_ofName(v_method_1577_);
v___x_1660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1658_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__21, &l_Lean_Server_registerRpcProcedure___closed__21_once, _init_l_Lean_Server_registerRpcProcedure___closed__21);
v___x_1662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1660_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
v___x_1671_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(v___x_1583_, v_method_1577_);
lean_dec(v___x_1583_);
if (v___x_1671_ == 0)
{
v___y_1664_ = v_a_1578_;
v___y_1665_ = v_a_1579_;
goto v___jp_1663_;
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
lean_dec_ref(v_env_1584_);
lean_dec(v_method_1577_);
v___x_1672_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__24, &l_Lean_Server_registerRpcProcedure___closed__24_once, _init_l_Lean_Server_registerRpcProcedure___closed__24);
v___x_1673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1662_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v___x_1673_, v_a_1578_, v_a_1579_);
return v___x_1674_;
}
v___jp_1585_:
{
lean_object* v___x_1588_; uint8_t v___x_1589_; uint8_t v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___f_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1588_ = lean_box(0);
v___x_1589_ = 1;
v___x_1590_ = 0;
v___x_1591_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__2));
v___x_1592_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__9, &l_Lean_Server_registerRpcProcedure___closed__9_once, _init_l_Lean_Server_registerRpcProcedure___closed__9);
v___x_1593_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__13, &l_Lean_Server_registerRpcProcedure___closed__13_once, _init_l_Lean_Server_registerRpcProcedure___closed__13);
v___x_1594_ = lean_st_mk_ref(v___x_1593_);
v___x_1595_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_1596_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_1597_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__14, &l_Lean_Server_registerRpcProcedure___closed__14_once, _init_l_Lean_Server_registerRpcProcedure___closed__14);
v___x_1598_ = lean_box(v___x_1590_);
v___x_1599_ = lean_box(v___x_1589_);
lean_inc(v_method_1577_);
v___f_1600_ = lean_alloc_closure((void*)(l_Lean_Server_registerRpcProcedure___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1600_, 0, v___x_1598_);
lean_closure_set(v___f_1600_, 1, v___x_1595_);
lean_closure_set(v___f_1600_, 2, v___x_1596_);
lean_closure_set(v___f_1600_, 3, v_method_1577_);
lean_closure_set(v___f_1600_, 4, v___x_1597_);
lean_closure_set(v___f_1600_, 5, v___x_1599_);
v___x_1601_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___boxed), 9, 2);
lean_closure_set(v___x_1601_, 0, lean_box(0));
lean_closure_set(v___x_1601_, 1, v___f_1600_);
v___x_1602_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__15));
v___x_1603_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_1601_, v___x_1591_, v___x_1602_, v___x_1592_, v___x_1594_, v___y_1586_, v___y_1587_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1605_; lean_object* v_fst_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1647_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref(v___x_1603_);
v___x_1605_ = lean_st_ref_get(v___x_1594_);
lean_dec(v___x_1594_);
lean_dec(v___x_1605_);
v_fst_1606_ = lean_ctor_get(v_a_1604_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_a_1604_);
if (v_isSharedCheck_1647_ == 0)
{
lean_object* v_unused_1648_; 
v_unused_1648_ = lean_ctor_get(v_a_1604_, 1);
lean_dec(v_unused_1648_);
v___x_1608_ = v_a_1604_;
v_isShared_1609_ = v_isSharedCheck_1647_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_fst_1606_);
lean_dec(v_a_1604_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1647_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; lean_object* v___x_1616_; 
v___x_1610_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__17));
lean_inc(v_method_1577_);
v___x_1611_ = l_Lean_Name_append(v_method_1577_, v___x_1610_);
lean_inc_n(v___x_1611_, 2);
v___x_1612_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
lean_ctor_set(v___x_1612_, 1, v___x_1588_);
lean_ctor_set(v___x_1612_, 2, v___x_1597_);
v___x_1613_ = lean_box(0);
v___x_1614_ = 1;
if (v_isShared_1609_ == 0)
{
lean_ctor_set_tag(v___x_1608_, 1);
lean_ctor_set(v___x_1608_, 1, v___x_1588_);
lean_ctor_set(v___x_1608_, 0, v___x_1611_);
v___x_1616_ = v___x_1608_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v___x_1588_);
v___x_1616_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1617_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1617_, 0, v___x_1612_);
lean_ctor_set(v___x_1617_, 1, v_fst_1606_);
lean_ctor_set(v___x_1617_, 2, v___x_1613_);
lean_ctor_set(v___x_1617_, 3, v___x_1616_);
lean_ctor_set_uint8(v___x_1617_, sizeof(void*)*4, v___x_1614_);
v___x_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
lean_inc_ref(v___x_1618_);
v___x_1619_ = l_Lean_addDecl(v___x_1618_, v___x_1590_, v___y_1586_, v___y_1587_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v___x_1620_; lean_object* v_env_1621_; lean_object* v_nextMacroScope_1622_; lean_object* v_ngen_1623_; lean_object* v_auxDeclNGen_1624_; lean_object* v_traceState_1625_; lean_object* v_messages_1626_; lean_object* v_infoState_1627_; lean_object* v_snapshotTasks_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1644_; 
lean_dec_ref(v___x_1619_);
v___x_1620_ = lean_st_ref_take(v___y_1587_);
v_env_1621_ = lean_ctor_get(v___x_1620_, 0);
v_nextMacroScope_1622_ = lean_ctor_get(v___x_1620_, 1);
v_ngen_1623_ = lean_ctor_get(v___x_1620_, 2);
v_auxDeclNGen_1624_ = lean_ctor_get(v___x_1620_, 3);
v_traceState_1625_ = lean_ctor_get(v___x_1620_, 4);
v_messages_1626_ = lean_ctor_get(v___x_1620_, 6);
v_infoState_1627_ = lean_ctor_get(v___x_1620_, 7);
v_snapshotTasks_1628_ = lean_ctor_get(v___x_1620_, 8);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1644_ == 0)
{
lean_object* v_unused_1645_; 
v_unused_1645_ = lean_ctor_get(v___x_1620_, 5);
lean_dec(v_unused_1645_);
v___x_1630_ = v___x_1620_;
v_isShared_1631_ = v_isSharedCheck_1644_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_snapshotTasks_1628_);
lean_inc(v_infoState_1627_);
lean_inc(v_messages_1626_);
lean_inc(v_traceState_1625_);
lean_inc(v_auxDeclNGen_1624_);
lean_inc(v_ngen_1623_);
lean_inc(v_nextMacroScope_1622_);
lean_inc(v_env_1621_);
lean_dec(v___x_1620_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1644_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1635_; 
lean_inc(v___x_1611_);
v___x_1632_ = l_Lean_markMeta(v_env_1621_, v___x_1611_);
v___x_1633_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__18, &l_Lean_Server_registerRpcProcedure___closed__18_once, _init_l_Lean_Server_registerRpcProcedure___closed__18);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 5, v___x_1633_);
lean_ctor_set(v___x_1630_, 0, v___x_1632_);
v___x_1635_ = v___x_1630_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_nextMacroScope_1622_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_ngen_1623_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v_auxDeclNGen_1624_);
lean_ctor_set(v_reuseFailAlloc_1643_, 4, v_traceState_1625_);
lean_ctor_set(v_reuseFailAlloc_1643_, 5, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1643_, 6, v_messages_1626_);
lean_ctor_set(v_reuseFailAlloc_1643_, 7, v_infoState_1627_);
lean_ctor_set(v_reuseFailAlloc_1643_, 8, v_snapshotTasks_1628_);
v___x_1635_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = lean_st_ref_set(v___y_1587_, v___x_1635_);
v___x_1637_ = l_Lean_compileDecl(v___x_1618_, v___x_1589_, v___y_1586_, v___y_1587_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v___x_1638_; lean_object* v_env_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
lean_dec_ref(v___x_1637_);
v___x_1638_ = lean_st_ref_get(v___y_1587_);
v_env_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc_ref(v_env_1639_);
lean_dec(v___x_1638_);
v___x_1640_ = l_Lean_Server_userRpcProcedures;
v___x_1641_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1640_, v_env_1639_, v_method_1577_, v___x_1611_);
v___x_1642_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(v___x_1641_, v___y_1587_);
return v___x_1642_;
}
else
{
lean_dec(v___x_1611_);
lean_dec(v_method_1577_);
return v___x_1637_;
}
}
}
}
else
{
lean_dec_ref(v___x_1618_);
lean_dec(v___x_1611_);
lean_dec(v_method_1577_);
return v___x_1619_;
}
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v___x_1594_);
lean_dec(v_method_1577_);
v_a_1649_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1603_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1603_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
v___jp_1663_:
{
lean_object* v___x_1666_; uint8_t v___x_1667_; 
v___x_1666_ = l_Lean_Server_userRpcProcedures;
lean_inc(v_method_1577_);
v___x_1667_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_1657_, v___x_1666_, v_env_1584_, v_method_1577_);
if (v___x_1667_ == 0)
{
lean_dec_ref(v___x_1662_);
v___y_1586_ = v___y_1664_;
v___y_1587_ = v___y_1665_;
goto v___jp_1585_;
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_dec(v_method_1577_);
v___x_1668_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__22, &l_Lean_Server_registerRpcProcedure___closed__22_once, _init_l_Lean_Server_registerRpcProcedure___closed__22);
v___x_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1662_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v___x_1669_, v___y_1664_, v___y_1665_);
return v___x_1670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___boxed(lean_object* v_method_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_Server_registerRpcProcedure(v_method_1675_, v_a_1676_, v_a_1677_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3(lean_object* v_00_u03b1_1680_, lean_object* v_msg_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v_msg_1681_, v___y_1682_, v___y_1683_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___boxed(lean_object* v_00_u03b1_1686_, lean_object* v_msg_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3(v_00_u03b1_1686_, v_msg_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(lean_object* v___x_1692_, lean_object* v_decl_1693_, lean_object* v_x_1694_, uint8_t v_attrKind_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v___x_1699_; 
lean_inc(v_decl_1693_);
v___x_1699_ = l_Lean_ensureAttrDeclIsMeta(v___x_1692_, v_decl_1693_, v_attrKind_1695_, v___y_1696_, v___y_1697_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v___x_1700_; 
lean_dec_ref(v___x_1699_);
v___x_1700_ = l_Lean_Server_registerRpcProcedure(v_decl_1693_, v___y_1696_, v___y_1697_);
return v___x_1700_;
}
else
{
lean_dec(v_decl_1693_);
return v___x_1699_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed(lean_object* v___x_1701_, lean_object* v_decl_1702_, lean_object* v_x_1703_, lean_object* v_attrKind_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
uint8_t v_attrKind_boxed_1708_; lean_object* v_res_1709_; 
v_attrKind_boxed_1708_ = lean_unbox(v_attrKind_1704_);
v_res_1709_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(v___x_1701_, v_decl_1702_, v_x_1703_, v_attrKind_boxed_1708_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v_x_1703_);
return v_res_1709_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_));
v___x_1712_ = l_Lean_stringToMessageData(v___x_1711_);
return v___x_1712_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_));
v___x_1715_ = l_Lean_stringToMessageData(v___x_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(lean_object* v___x_1716_, lean_object* v_decl_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1721_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_);
v___x_1722_ = l_Lean_MessageData_ofName(v___x_1716_);
v___x_1723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1721_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
v___x_1724_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_);
v___x_1725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1723_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
v___x_1726_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v___x_1725_, v___y_1718_, v___y_1719_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed(lean_object* v___x_1727_, lean_object* v_decl_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(v___x_1727_, v_decl_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v_decl_1728_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__31_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_));
v___x_1813_ = l_Lean_registerBuiltinAttribute(v___x_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed(lean_object* v_a_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_();
return v_res_1815_;
}
}
lean_object* runtime_initialize_Lean_Server_Requests(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Rpc_RequestHandling(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Server_Requests(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures);
lean_dec_ref(res);
res = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_userRpcProcedures = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_userRpcProcedures);
lean_dec_ref(res);
res = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_Rpc_RequestHandling(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_Requests(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Rpc_RequestHandling(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_Requests(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Rpc_RequestHandling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_Rpc_RequestHandling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_Rpc_RequestHandling(builtin);
}
#ifdef __cplusplus
}
#endif
