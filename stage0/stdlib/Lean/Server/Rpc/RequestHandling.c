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
lean_object* v_es_381_; lean_object* v___x_382_; size_t v___x_383_; size_t v___x_384_; size_t v___x_385_; lean_object* v_j_386_; lean_object* v___x_387_; 
v_es_381_ = lean_ctor_get(v_x_378_, 0);
v___x_382_ = lean_box(2);
v___x_383_ = ((size_t)5ULL);
v___x_384_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1);
v___x_385_ = lean_usize_land(v_x_379_, v___x_384_);
v_j_386_ = lean_usize_to_nat(v___x_385_);
v___x_387_ = lean_array_get_borrowed(v___x_382_, v_es_381_, v_j_386_);
lean_dec(v_j_386_);
switch(lean_obj_tag(v___x_387_))
{
case 0:
{
lean_object* v_key_388_; lean_object* v_val_389_; uint8_t v___x_390_; 
v_key_388_ = lean_ctor_get(v___x_387_, 0);
v_val_389_ = lean_ctor_get(v___x_387_, 1);
v___x_390_ = lean_name_eq(v_x_380_, v_key_388_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
v___x_391_ = lean_box(0);
return v___x_391_;
}
else
{
lean_object* v___x_392_; 
lean_inc(v_val_389_);
v___x_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_392_, 0, v_val_389_);
return v___x_392_;
}
}
case 1:
{
lean_object* v_node_393_; size_t v___x_394_; 
v_node_393_ = lean_ctor_get(v___x_387_, 0);
v___x_394_ = lean_usize_shift_right(v_x_379_, v___x_383_);
v_x_378_ = v_node_393_;
v_x_379_ = v___x_394_;
goto _start;
}
default: 
{
lean_object* v___x_396_; 
v___x_396_ = lean_box(0);
return v___x_396_;
}
}
}
else
{
lean_object* v_ks_397_; lean_object* v_vs_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_ks_397_ = lean_ctor_get(v_x_378_, 0);
v_vs_398_ = lean_ctor_get(v_x_378_, 1);
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(v_ks_397_, v_vs_398_, v___x_399_, v_x_380_);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg___boxed(lean_object* v_x_401_, lean_object* v_x_402_, lean_object* v_x_403_){
_start:
{
size_t v_x_2428__boxed_404_; lean_object* v_res_405_; 
v_x_2428__boxed_404_ = lean_unbox_usize(v_x_402_);
lean_dec(v_x_402_);
v_res_405_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(v_x_401_, v_x_2428__boxed_404_, v_x_403_);
lean_dec(v_x_403_);
lean_dec_ref(v_x_401_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(lean_object* v_x_406_, lean_object* v_x_407_){
_start:
{
uint64_t v___y_409_; 
if (lean_obj_tag(v_x_407_) == 0)
{
uint64_t v___x_412_; 
v___x_412_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___closed__0);
v___y_409_ = v___x_412_;
goto v___jp_408_;
}
else
{
uint64_t v_hash_413_; 
v_hash_413_ = lean_ctor_get_uint64(v_x_407_, sizeof(void*)*2);
v___y_409_ = v_hash_413_;
goto v___jp_408_;
}
v___jp_408_:
{
size_t v___x_410_; lean_object* v___x_411_; 
v___x_410_ = lean_uint64_to_usize(v___y_409_);
v___x_411_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(v_x_406_, v___x_410_, v_x_407_);
return v___x_411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg___boxed(lean_object* v_x_414_, lean_object* v_x_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(v_x_414_, v_x_415_);
lean_dec(v_x_415_);
lean_dec_ref(v_x_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall(lean_object* v_p_419_, lean_object* v_a_420_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v_toTextDocumentPositionParams_424_; uint64_t v_sessionId_425_; lean_object* v_method_426_; lean_object* v_params_427_; lean_object* v___x_428_; 
v___x_422_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_423_ = lean_st_ref_get(v___x_422_);
v_toTextDocumentPositionParams_424_ = lean_ctor_get(v_p_419_, 0);
lean_inc_ref(v_toTextDocumentPositionParams_424_);
v_sessionId_425_ = lean_ctor_get_uint64(v_p_419_, sizeof(void*)*3);
v_method_426_ = lean_ctor_get(v_p_419_, 1);
lean_inc(v_method_426_);
v_params_427_ = lean_ctor_get(v_p_419_, 2);
lean_inc(v_params_427_);
lean_dec_ref(v_p_419_);
v___x_428_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(v___x_423_, v_method_426_);
lean_dec(v___x_423_);
if (lean_obj_tag(v___x_428_) == 1)
{
lean_object* v_val_429_; lean_object* v___x_430_; lean_object* v___f_431_; lean_object* v___x_432_; 
lean_dec(v_method_426_);
lean_dec_ref(v_toTextDocumentPositionParams_424_);
v_val_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_val_429_);
lean_dec_ref(v___x_428_);
v___x_430_ = lean_box_uint64(v_sessionId_425_);
v___f_431_ = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__0___boxed), 5, 3);
lean_closure_set(v___f_431_, 0, v_val_429_);
lean_closure_set(v___f_431_, 1, v___x_430_);
lean_closure_set(v___f_431_, 2, v_params_427_);
v___x_432_ = l_Lean_Server_RequestM_asTask___redArg(v___f_431_, v_a_420_);
return v___x_432_;
}
else
{
lean_object* v___x_433_; lean_object* v_a_434_; lean_object* v_toEditableDocumentCore_435_; lean_object* v_meta_436_; lean_object* v_text_437_; lean_object* v_position_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___f_442_; uint8_t v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___f_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___f_454_; lean_object* v___x_455_; 
lean_dec(v___x_428_);
v___x_433_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1(v_a_420_);
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref(v___x_433_);
v_toEditableDocumentCore_435_ = lean_ctor_get(v_a_434_, 0);
v_meta_436_ = lean_ctor_get(v_toEditableDocumentCore_435_, 0);
v_text_437_ = lean_ctor_get(v_meta_436_, 3);
v_position_438_ = lean_ctor_get(v_toTextDocumentPositionParams_424_, 1);
lean_inc_ref(v_position_438_);
lean_dec_ref(v_toTextDocumentPositionParams_424_);
v___x_439_ = lean_box(0);
v___x_440_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_441_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_437_, v_position_438_);
lean_inc_n(v_method_426_, 2);
v___f_442_ = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__1___boxed), 4, 3);
lean_closure_set(v___f_442_, 0, v___x_441_);
lean_closure_set(v___f_442_, 1, v___x_439_);
lean_closure_set(v___f_442_, 2, v_method_426_);
v___x_443_ = 2;
v___x_444_ = ((lean_object*)(l_Lean_Server_handleRpcCall___closed__0));
v___x_445_ = 1;
v___x_446_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_426_, v___x_445_);
v___x_447_ = lean_string_append(v___x_444_, v___x_446_);
lean_dec_ref(v___x_446_);
v___x_448_ = ((lean_object*)(l_Lean_Server_handleRpcCall___closed__1));
v___x_449_ = lean_string_append(v___x_447_, v___x_448_);
v___x_450_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_450_, 0, v___x_449_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*1, v___x_443_);
lean_inc_ref(v___x_450_);
v___f_451_ = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__2___boxed), 3, 1);
lean_closure_set(v___f_451_, 0, v___x_450_);
v___x_452_ = lean_box(v___x_445_);
v___x_453_ = lean_box_uint64(v_sessionId_425_);
v___f_454_ = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__3___boxed), 10, 7);
lean_closure_set(v___f_454_, 0, v___x_439_);
lean_closure_set(v___f_454_, 1, v_method_426_);
lean_closure_set(v___f_454_, 2, v___x_440_);
lean_closure_set(v___f_454_, 3, v___x_452_);
lean_closure_set(v___f_454_, 4, v___x_453_);
lean_closure_set(v___f_454_, 5, v_params_427_);
lean_closure_set(v___f_454_, 6, v___x_450_);
v___x_455_ = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(v_a_434_, v___f_442_, v___f_451_, v___f_454_, v_a_420_);
return v___x_455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___boxed(lean_object* v_p_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_Server_handleRpcCall(v_p_456_, v_a_457_);
lean_dec_ref(v_a_457_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0(lean_object* v_00_u03b2_460_, lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(v_x_461_, v_x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___boxed(lean_object* v_00_u03b2_464_, lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0(v_00_u03b2_464_, v_x_465_, v_x_466_);
lean_dec(v_x_466_);
lean_dec_ref(v_x_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0(lean_object* v_00_u03b2_468_, lean_object* v_x_469_, size_t v_x_470_, lean_object* v_x_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(v_x_469_, v_x_470_, v_x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___boxed(lean_object* v_00_u03b2_473_, lean_object* v_x_474_, lean_object* v_x_475_, lean_object* v_x_476_){
_start:
{
size_t v_x_2566__boxed_477_; lean_object* v_res_478_; 
v_x_2566__boxed_477_ = lean_unbox_usize(v_x_475_);
lean_dec(v_x_475_);
v_res_478_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0(v_00_u03b2_473_, v_x_474_, v_x_2566__boxed_477_, v_x_476_);
lean_dec(v_x_476_);
lean_dec_ref(v_x_474_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_479_, lean_object* v_keys_480_, lean_object* v_vals_481_, lean_object* v_heq_482_, lean_object* v_i_483_, lean_object* v_k_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(v_keys_480_, v_vals_481_, v_i_483_, v_k_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_486_, lean_object* v_keys_487_, lean_object* v_vals_488_, lean_object* v_heq_489_, lean_object* v_i_490_, lean_object* v_k_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2(v_00_u03b2_486_, v_keys_487_, v_vals_488_, v_heq_489_, v_i_490_, v_k_491_);
lean_dec(v_k_491_);
lean_dec_ref(v_vals_488_);
lean_dec_ref(v_keys_487_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_493_, uint8_t v_a_494_, lean_object* v___y_495_){
_start:
{
if (lean_obj_tag(v___y_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec(v_serialize_x3f_493_);
v_a_496_ = lean_ctor_get(v___y_495_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___y_495_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___y_495_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___y_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
else
{
if (lean_obj_tag(v_serialize_x3f_493_) == 1)
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_515_; 
v_a_504_ = lean_ctor_get(v___y_495_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___y_495_);
if (v_isSharedCheck_515_ == 0)
{
v___x_506_ = v___y_495_;
v_isShared_507_ = v_isSharedCheck_515_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___y_495_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_515_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v_val_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v_val_508_ = lean_ctor_get(v_serialize_x3f_493_, 0);
lean_inc(v_val_508_);
lean_dec_ref(v_serialize_x3f_493_);
v___x_509_ = lean_box(0);
v___x_510_ = lean_apply_1(v_val_508_, v_a_504_);
v___x_511_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_511_, 0, v___x_509_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*2, v_a_494_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_511_);
v___x_513_ = v___x_506_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_526_; 
lean_dec(v_serialize_x3f_493_);
v_a_516_ = lean_ctor_get(v___y_495_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___y_495_);
if (v_isSharedCheck_526_ == 0)
{
v___x_518_ = v___y_495_;
v_isShared_519_ = v_isSharedCheck_526_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___y_495_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_526_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_524_; 
lean_inc(v_a_516_);
v___x_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_520_, 0, v_a_516_);
v___x_521_ = l_Lean_Json_compress(v_a_516_);
v___x_522_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*2, v_a_494_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_522_);
v___x_524_ = v___x_518_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_527_, lean_object* v_a_528_, lean_object* v___y_529_){
_start:
{
uint8_t v_a_666__boxed_530_; lean_object* v_res_531_; 
v_a_666__boxed_530_ = lean_unbox(v_a_528_);
v_res_531_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_527_, v_a_666__boxed_530_, v___y_529_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8___redArg(lean_object* v_x_532_, lean_object* v_x_533_, lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
lean_object* v_ks_536_; lean_object* v_vs_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_561_; 
v_ks_536_ = lean_ctor_get(v_x_532_, 0);
v_vs_537_ = lean_ctor_get(v_x_532_, 1);
v_isSharedCheck_561_ = !lean_is_exclusive(v_x_532_);
if (v_isSharedCheck_561_ == 0)
{
v___x_539_ = v_x_532_;
v_isShared_540_ = v_isSharedCheck_561_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_vs_537_);
lean_inc(v_ks_536_);
lean_dec(v_x_532_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_561_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_541_ = lean_array_get_size(v_ks_536_);
v___x_542_ = lean_nat_dec_lt(v_x_533_, v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_546_; 
lean_dec(v_x_533_);
v___x_543_ = lean_array_push(v_ks_536_, v_x_534_);
v___x_544_ = lean_array_push(v_vs_537_, v_x_535_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_544_);
lean_ctor_set(v___x_539_, 0, v___x_543_);
v___x_546_ = v___x_539_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
else
{
lean_object* v_k_x27_548_; uint8_t v___x_549_; 
v_k_x27_548_ = lean_array_fget_borrowed(v_ks_536_, v_x_533_);
v___x_549_ = lean_string_dec_eq(v_x_534_, v_k_x27_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_551_; 
if (v_isShared_540_ == 0)
{
v___x_551_ = v___x_539_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_ks_536_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_vs_537_);
v___x_551_ = v_reuseFailAlloc_555_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_unsigned_to_nat(1u);
v___x_553_ = lean_nat_add(v_x_533_, v___x_552_);
lean_dec(v_x_533_);
v_x_532_ = v___x_551_;
v_x_533_ = v___x_553_;
goto _start;
}
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_556_ = lean_array_fset(v_ks_536_, v_x_533_, v_x_534_);
v___x_557_ = lean_array_fset(v_vs_537_, v_x_533_, v_x_535_);
lean_dec(v_x_533_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_557_);
lean_ctor_set(v___x_539_, 0, v___x_556_);
v___x_559_ = v___x_539_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7___redArg(lean_object* v_n_562_, lean_object* v_k_563_, lean_object* v_v_564_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8___redArg(v_n_562_, v___x_565_, v_k_563_, v_v_564_);
return v___x_566_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* v_x_568_, size_t v_x_569_, size_t v_x_570_, lean_object* v_x_571_, lean_object* v_x_572_){
_start:
{
if (lean_obj_tag(v_x_568_) == 0)
{
lean_object* v_es_573_; size_t v___x_574_; size_t v___x_575_; size_t v___x_576_; size_t v___x_577_; lean_object* v_j_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v_es_573_ = lean_ctor_get(v_x_568_, 0);
v___x_574_ = ((size_t)5ULL);
v___x_575_ = ((size_t)1ULL);
v___x_576_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1);
v___x_577_ = lean_usize_land(v_x_569_, v___x_576_);
v_j_578_ = lean_usize_to_nat(v___x_577_);
v___x_579_ = lean_array_get_size(v_es_573_);
v___x_580_ = lean_nat_dec_lt(v_j_578_, v___x_579_);
if (v___x_580_ == 0)
{
lean_dec(v_j_578_);
lean_dec(v_x_572_);
lean_dec_ref(v_x_571_);
return v_x_568_;
}
else
{
lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_617_; 
lean_inc_ref(v_es_573_);
v_isSharedCheck_617_ = !lean_is_exclusive(v_x_568_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; 
v_unused_618_ = lean_ctor_get(v_x_568_, 0);
lean_dec(v_unused_618_);
v___x_582_ = v_x_568_;
v_isShared_583_ = v_isSharedCheck_617_;
goto v_resetjp_581_;
}
else
{
lean_dec(v_x_568_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_617_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v_v_584_; lean_object* v___x_585_; lean_object* v_xs_x27_586_; lean_object* v___y_588_; 
v_v_584_ = lean_array_fget(v_es_573_, v_j_578_);
v___x_585_ = lean_box(0);
v_xs_x27_586_ = lean_array_fset(v_es_573_, v_j_578_, v___x_585_);
switch(lean_obj_tag(v_v_584_))
{
case 0:
{
lean_object* v_key_593_; lean_object* v_val_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_604_; 
v_key_593_ = lean_ctor_get(v_v_584_, 0);
v_val_594_ = lean_ctor_get(v_v_584_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_v_584_);
if (v_isSharedCheck_604_ == 0)
{
v___x_596_ = v_v_584_;
v_isShared_597_ = v_isSharedCheck_604_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_val_594_);
lean_inc(v_key_593_);
lean_dec(v_v_584_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_604_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
uint8_t v___x_598_; 
v___x_598_ = lean_string_dec_eq(v_x_571_, v_key_593_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; 
lean_del_object(v___x_596_);
v___x_599_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_593_, v_val_594_, v_x_571_, v_x_572_);
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
v___y_588_ = v___x_600_;
goto v___jp_587_;
}
else
{
lean_object* v___x_602_; 
lean_dec(v_val_594_);
lean_dec(v_key_593_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 1, v_x_572_);
lean_ctor_set(v___x_596_, 0, v_x_571_);
v___x_602_ = v___x_596_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_x_571_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_x_572_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
v___y_588_ = v___x_602_;
goto v___jp_587_;
}
}
}
}
case 1:
{
lean_object* v_node_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_615_; 
v_node_605_ = lean_ctor_get(v_v_584_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v_v_584_);
if (v_isSharedCheck_615_ == 0)
{
v___x_607_ = v_v_584_;
v_isShared_608_ = v_isSharedCheck_615_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_node_605_);
lean_dec(v_v_584_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_615_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
size_t v___x_609_; size_t v___x_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_609_ = lean_usize_shift_right(v_x_569_, v___x_574_);
v___x_610_ = lean_usize_add(v_x_570_, v___x_575_);
v___x_611_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_node_605_, v___x_609_, v___x_610_, v_x_571_, v_x_572_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_611_);
v___x_613_ = v___x_607_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
v___y_588_ = v___x_613_;
goto v___jp_587_;
}
}
}
default: 
{
lean_object* v___x_616_; 
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v_x_571_);
lean_ctor_set(v___x_616_, 1, v_x_572_);
v___y_588_ = v___x_616_;
goto v___jp_587_;
}
}
v___jp_587_:
{
lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_589_ = lean_array_fset(v_xs_x27_586_, v_j_578_, v___y_588_);
lean_dec(v_j_578_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_589_);
v___x_591_ = v___x_582_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
else
{
lean_object* v_ks_619_; lean_object* v_vs_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_640_; 
v_ks_619_ = lean_ctor_get(v_x_568_, 0);
v_vs_620_ = lean_ctor_get(v_x_568_, 1);
v_isSharedCheck_640_ = !lean_is_exclusive(v_x_568_);
if (v_isSharedCheck_640_ == 0)
{
v___x_622_ = v_x_568_;
v_isShared_623_ = v_isSharedCheck_640_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_vs_620_);
lean_inc(v_ks_619_);
lean_dec(v_x_568_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_640_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_ks_619_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_vs_620_);
v___x_625_ = v_reuseFailAlloc_639_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v_newNode_626_; uint8_t v___y_628_; size_t v___x_634_; uint8_t v___x_635_; 
v_newNode_626_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7___redArg(v___x_625_, v_x_571_, v_x_572_);
v___x_634_ = ((size_t)7ULL);
v___x_635_ = lean_usize_dec_le(v___x_634_, v_x_570_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_636_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_626_);
v___x_637_ = lean_unsigned_to_nat(4u);
v___x_638_ = lean_nat_dec_lt(v___x_636_, v___x_637_);
lean_dec(v___x_636_);
v___y_628_ = v___x_638_;
goto v___jp_627_;
}
else
{
v___y_628_ = v___x_635_;
goto v___jp_627_;
}
v___jp_627_:
{
if (v___y_628_ == 0)
{
lean_object* v_ks_629_; lean_object* v_vs_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v_ks_629_ = lean_ctor_get(v_newNode_626_, 0);
lean_inc_ref(v_ks_629_);
v_vs_630_ = lean_ctor_get(v_newNode_626_, 1);
lean_inc_ref(v_vs_630_);
lean_dec_ref(v_newNode_626_);
v___x_631_ = lean_unsigned_to_nat(0u);
v___x_632_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
v___x_633_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_x_570_, v_ks_629_, v_vs_630_, v___x_631_, v___x_632_);
lean_dec_ref(v_vs_630_);
lean_dec_ref(v_ks_629_);
return v___x_633_;
}
else
{
return v_newNode_626_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(size_t v_depth_641_, lean_object* v_keys_642_, lean_object* v_vals_643_, lean_object* v_i_644_, lean_object* v_entries_645_){
_start:
{
lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_646_ = lean_array_get_size(v_keys_642_);
v___x_647_ = lean_nat_dec_lt(v_i_644_, v___x_646_);
if (v___x_647_ == 0)
{
lean_dec(v_i_644_);
return v_entries_645_;
}
else
{
lean_object* v_k_648_; lean_object* v_v_649_; uint64_t v___x_650_; size_t v_h_651_; size_t v___x_652_; lean_object* v___x_653_; size_t v___x_654_; size_t v___x_655_; size_t v___x_656_; size_t v_h_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_k_648_ = lean_array_fget_borrowed(v_keys_642_, v_i_644_);
v_v_649_ = lean_array_fget_borrowed(v_vals_643_, v_i_644_);
v___x_650_ = lean_string_hash(v_k_648_);
v_h_651_ = lean_uint64_to_usize(v___x_650_);
v___x_652_ = ((size_t)5ULL);
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = ((size_t)1ULL);
v___x_655_ = lean_usize_sub(v_depth_641_, v___x_654_);
v___x_656_ = lean_usize_mul(v___x_652_, v___x_655_);
v_h_657_ = lean_usize_shift_right(v_h_651_, v___x_656_);
v___x_658_ = lean_nat_add(v_i_644_, v___x_653_);
lean_dec(v_i_644_);
lean_inc(v_v_649_);
lean_inc(v_k_648_);
v___x_659_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_entries_645_, v_h_657_, v_depth_641_, v_k_648_, v_v_649_);
v_i_644_ = v___x_658_;
v_entries_645_ = v___x_659_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_depth_661_, lean_object* v_keys_662_, lean_object* v_vals_663_, lean_object* v_i_664_, lean_object* v_entries_665_){
_start:
{
size_t v_depth_boxed_666_; lean_object* v_res_667_; 
v_depth_boxed_666_ = lean_unbox_usize(v_depth_661_);
lean_dec(v_depth_661_);
v_res_667_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_depth_boxed_666_, v_keys_662_, v_vals_663_, v_i_664_, v_entries_665_);
lean_dec_ref(v_vals_663_);
lean_dec_ref(v_keys_662_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_x_668_, lean_object* v_x_669_, lean_object* v_x_670_, lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
size_t v_x_817__boxed_673_; size_t v_x_818__boxed_674_; lean_object* v_res_675_; 
v_x_817__boxed_673_ = lean_unbox_usize(v_x_669_);
lean_dec(v_x_669_);
v_x_818__boxed_674_ = lean_unbox_usize(v_x_670_);
lean_dec(v_x_670_);
v_res_675_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_668_, v_x_817__boxed_673_, v_x_818__boxed_674_, v_x_671_, v_x_672_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* v_x_676_, lean_object* v_x_677_, lean_object* v_x_678_){
_start:
{
uint64_t v___x_679_; size_t v___x_680_; size_t v___x_681_; lean_object* v___x_682_; 
v___x_679_ = lean_string_hash(v_x_677_);
v___x_680_ = lean_uint64_to_usize(v___x_679_);
v___x_681_ = ((size_t)1ULL);
v___x_682_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_676_, v___x_680_, v___x_681_, v_x_677_, v_x_678_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_685_){
_start:
{
lean_object* v___x_686_; 
lean_inc(v_params_685_);
v___x_686_ = l_Lean_Lsp_instFromJsonRpcCallParams_fromJson(v_params_685_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_702_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_702_ == 0)
{
v___x_689_ = v___x_686_;
v_isShared_690_ = v_isSharedCheck_702_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_686_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_702_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
uint8_t v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_691_ = 3;
v___x_692_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_693_ = l_Lean_Json_compress(v_params_685_);
v___x_694_ = lean_string_append(v___x_692_, v___x_693_);
lean_dec_ref(v___x_693_);
v___x_695_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__1));
v___x_696_ = lean_string_append(v___x_694_, v___x_695_);
v___x_697_ = lean_string_append(v___x_696_, v_a_687_);
lean_dec(v_a_687_);
v___x_698_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set_uint8(v___x_698_, sizeof(void*)*1, v___x_691_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_698_);
v___x_700_ = v___x_689_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec(v_params_685_);
v_a_703_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_686_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_686_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_711_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0(v_params_711_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
lean_ctor_set_tag(v___x_716_, 1);
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
v_a_722_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_713_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_713_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
lean_ctor_set_tag(v___x_724_, 0);
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_730_, lean_object* v_a_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_733_, lean_object* v___f_734_, lean_object* v_j_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_735_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref(v___x_738_);
lean_inc_ref(v___y_736_);
v___x_740_ = lean_apply_3(v_handler_733_, v_a_739_, v___y_736_, lean_box(0));
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_749_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_749_ == 0)
{
v___x_743_ = v___x_740_;
v_isShared_744_ = v_isSharedCheck_749_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_749_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_745_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_734_, v_a_741_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_745_);
v___x_747_ = v___x_743_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec_ref(v___f_734_);
v_a_750_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_740_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_740_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
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
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec_ref(v___f_734_);
lean_dec_ref(v_handler_733_);
v_a_758_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_738_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_738_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_766_, lean_object* v___f_767_, lean_object* v_j_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2(v_handler_766_, v___f_767_, v_j_768_, v___y_769_);
lean_dec_ref(v___y_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0(v_j_772_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_791_; 
v_a_782_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_791_ == 0)
{
v___x_784_ = v___x_773_;
v_isShared_785_ = v_isSharedCheck_791_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_773_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_791_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v_toTextDocumentPositionParams_786_; lean_object* v_textDocument_787_; lean_object* v___x_789_; 
v_toTextDocumentPositionParams_786_ = lean_ctor_get(v_a_782_, 0);
lean_inc_ref(v_toTextDocumentPositionParams_786_);
lean_dec(v_a_782_);
v_textDocument_787_ = lean_ctor_get(v_toTextDocumentPositionParams_786_, 0);
lean_inc_ref(v_textDocument_787_);
lean_dec_ref(v_toTextDocumentPositionParams_786_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v_textDocument_787_);
v___x_789_ = v___x_784_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_textDocument_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_keys_792_, lean_object* v_i_793_, lean_object* v_k_794_){
_start:
{
lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_795_ = lean_array_get_size(v_keys_792_);
v___x_796_ = lean_nat_dec_lt(v_i_793_, v___x_795_);
if (v___x_796_ == 0)
{
lean_dec(v_i_793_);
return v___x_796_;
}
else
{
lean_object* v_k_x27_797_; uint8_t v___x_798_; 
v_k_x27_797_ = lean_array_fget_borrowed(v_keys_792_, v_i_793_);
v___x_798_ = lean_string_dec_eq(v_k_794_, v_k_x27_797_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_unsigned_to_nat(1u);
v___x_800_ = lean_nat_add(v_i_793_, v___x_799_);
lean_dec(v_i_793_);
v_i_793_ = v___x_800_;
goto _start;
}
else
{
lean_dec(v_i_793_);
return v___x_798_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_keys_802_, lean_object* v_i_803_, lean_object* v_k_804_){
_start:
{
uint8_t v_res_805_; lean_object* v_r_806_; 
v_res_805_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(v_keys_802_, v_i_803_, v_k_804_);
lean_dec_ref(v_k_804_);
lean_dec_ref(v_keys_802_);
v_r_806_ = lean_box(v_res_805_);
return v_r_806_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object* v_x_807_, size_t v_x_808_, lean_object* v_x_809_){
_start:
{
if (lean_obj_tag(v_x_807_) == 0)
{
lean_object* v_es_810_; lean_object* v___x_811_; size_t v___x_812_; size_t v___x_813_; size_t v___x_814_; lean_object* v_j_815_; lean_object* v___x_816_; 
v_es_810_ = lean_ctor_get(v_x_807_, 0);
v___x_811_ = lean_box(2);
v___x_812_ = ((size_t)5ULL);
v___x_813_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1);
v___x_814_ = lean_usize_land(v_x_808_, v___x_813_);
v_j_815_ = lean_usize_to_nat(v___x_814_);
v___x_816_ = lean_array_get_borrowed(v___x_811_, v_es_810_, v_j_815_);
lean_dec(v_j_815_);
switch(lean_obj_tag(v___x_816_))
{
case 0:
{
lean_object* v_key_817_; uint8_t v___x_818_; 
v_key_817_ = lean_ctor_get(v___x_816_, 0);
v___x_818_ = lean_string_dec_eq(v_x_809_, v_key_817_);
return v___x_818_;
}
case 1:
{
lean_object* v_node_819_; size_t v___x_820_; 
v_node_819_ = lean_ctor_get(v___x_816_, 0);
v___x_820_ = lean_usize_shift_right(v_x_808_, v___x_812_);
v_x_807_ = v_node_819_;
v_x_808_ = v___x_820_;
goto _start;
}
default: 
{
uint8_t v___x_822_; 
v___x_822_ = 0;
return v___x_822_;
}
}
}
else
{
lean_object* v_ks_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v_ks_823_ = lean_ctor_get(v_x_807_, 0);
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(v_ks_823_, v___x_824_, v_x_809_);
return v___x_825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_x_826_, lean_object* v_x_827_, lean_object* v_x_828_){
_start:
{
size_t v_x_1197__boxed_829_; uint8_t v_res_830_; lean_object* v_r_831_; 
v_x_1197__boxed_829_ = lean_unbox_usize(v_x_827_);
lean_dec(v_x_827_);
v_res_830_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_826_, v_x_1197__boxed_829_, v_x_828_);
lean_dec_ref(v_x_828_);
lean_dec_ref(v_x_826_);
v_r_831_ = lean_box(v_res_830_);
return v_r_831_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_832_, lean_object* v_x_833_){
_start:
{
uint64_t v___x_834_; size_t v___x_835_; uint8_t v___x_836_; 
v___x_834_ = lean_string_hash(v_x_833_);
v___x_835_ = lean_uint64_to_usize(v___x_834_);
v___x_836_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_832_, v___x_835_, v_x_833_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_x_837_, lean_object* v_x_838_){
_start:
{
uint8_t v_res_839_; lean_object* v_r_840_; 
v_res_839_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_837_, v_x_838_);
lean_dec_ref(v_x_838_);
lean_dec_ref(v_x_837_);
v_r_840_ = lean_box(v_res_839_);
return v_r_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0(lean_object* v_method_845_, lean_object* v_handler_846_, lean_object* v_serialize_x3f_847_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_initializing();
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_884_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_884_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_884_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_884_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
uint8_t v___x_854_; 
v___x_854_ = lean_unbox(v_a_850_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
lean_dec(v_a_850_);
lean_dec(v_serialize_x3f_847_);
lean_dec_ref(v_handler_846_);
v___x_855_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__0));
v___x_856_ = lean_string_append(v___x_855_, v_method_845_);
lean_dec_ref(v_method_845_);
v___x_857_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__1));
v___x_858_ = lean_string_append(v___x_856_, v___x_857_);
v___x_859_ = lean_mk_io_user_error(v___x_858_);
if (v_isShared_853_ == 0)
{
lean_ctor_set_tag(v___x_852_, 1);
lean_ctor_set(v___x_852_, 0, v___x_859_);
v___x_861_ = v___x_852_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
else
{
lean_object* v___x_863_; lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_863_ = l_Lean_Server_requestHandlers;
v___x_864_ = lean_st_ref_get(v___x_863_);
v___x_865_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_864_, v_method_845_);
lean_dec(v___x_864_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; lean_object* v___f_867_; lean_object* v___f_868_; lean_object* v___f_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_866_ = lean_st_ref_take(v___x_863_);
v___f_867_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__2));
v___f_868_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_868_, 0, v_serialize_x3f_847_);
lean_closure_set(v___f_868_, 1, v_a_850_);
v___f_869_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_869_, 0, v_handler_846_);
lean_closure_set(v___f_869_, 1, v___f_868_);
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v___f_867_);
lean_ctor_set(v___x_870_, 1, v___f_869_);
v___x_871_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_866_, v_method_845_, v___x_870_);
v___x_872_ = lean_st_ref_set(v___x_863_, v___x_871_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_872_);
v___x_874_ = v___x_852_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
else
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
lean_dec(v_a_850_);
lean_dec(v_serialize_x3f_847_);
lean_dec_ref(v_handler_846_);
v___x_876_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__0));
v___x_877_ = lean_string_append(v___x_876_, v_method_845_);
lean_dec_ref(v_method_845_);
v___x_878_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__3));
v___x_879_ = lean_string_append(v___x_877_, v___x_878_);
v___x_880_ = lean_mk_io_user_error(v___x_879_);
if (v_isShared_853_ == 0)
{
lean_ctor_set_tag(v___x_852_, 1);
lean_ctor_set(v___x_852_, 0, v___x_880_);
v___x_882_ = v___x_852_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec(v_serialize_x3f_847_);
lean_dec_ref(v_handler_846_);
lean_dec_ref(v_method_845_);
v_a_885_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_849_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_849_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_893_, lean_object* v_handler_894_, lean_object* v_serialize_x3f_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0(v_method_893_, v_handler_894_, v_serialize_x3f_895_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_901_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_));
v___x_902_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_));
v___x_903_ = lean_box(0);
v___x_904_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0(v___x_901_, v___x_902_, v___x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2____boxed(lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_();
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_907_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1(v_params_911_, v_a_912_);
lean_dec_ref(v_a_912_);
return v_res_914_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_915_, lean_object* v_x_916_, lean_object* v_x_917_){
_start:
{
uint8_t v___x_918_; 
v___x_918_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_916_, v_x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_919_, lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
uint8_t v_res_922_; lean_object* v_r_923_; 
v_res_922_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_919_, v_x_920_, v_x_921_);
lean_dec_ref(v_x_921_);
lean_dec_ref(v_x_920_);
v_r_923_ = lean_box(v_res_922_);
return v_r_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_00_u03b2_924_, lean_object* v_x_925_, lean_object* v_x_926_, lean_object* v_x_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_925_, v_x_926_, v_x_927_);
return v___x_928_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object* v_00_u03b2_929_, lean_object* v_x_930_, size_t v_x_931_, lean_object* v_x_932_){
_start:
{
uint8_t v___x_933_; 
v___x_933_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_930_, v_x_931_, v_x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_934_, lean_object* v_x_935_, lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
size_t v_x_1394__boxed_938_; uint8_t v_res_939_; lean_object* v_r_940_; 
v_x_1394__boxed_938_ = lean_unbox_usize(v_x_936_);
lean_dec(v_x_936_);
v_res_939_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_00_u03b2_934_, v_x_935_, v_x_1394__boxed_938_, v_x_937_);
lean_dec_ref(v_x_937_);
lean_dec_ref(v_x_935_);
v_r_940_ = lean_box(v_res_939_);
return v_r_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* v_00_u03b2_941_, lean_object* v_x_942_, size_t v_x_943_, size_t v_x_944_, lean_object* v_x_945_, lean_object* v_x_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_942_, v_x_943_, v_x_944_, v_x_945_, v_x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_948_, lean_object* v_x_949_, lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
size_t v_x_1405__boxed_954_; size_t v_x_1406__boxed_955_; lean_object* v_res_956_; 
v_x_1405__boxed_954_ = lean_unbox_usize(v_x_950_);
lean_dec(v_x_950_);
v_x_1406__boxed_955_ = lean_unbox_usize(v_x_951_);
lean_dec(v_x_951_);
v_res_956_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_948_, v_x_949_, v_x_1405__boxed_954_, v_x_1406__boxed_955_, v_x_952_, v_x_953_);
return v_res_956_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_957_, lean_object* v_keys_958_, lean_object* v_vals_959_, lean_object* v_heq_960_, lean_object* v_i_961_, lean_object* v_k_962_){
_start:
{
uint8_t v___x_963_; 
v___x_963_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(v_keys_958_, v_i_961_, v_k_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_964_, lean_object* v_keys_965_, lean_object* v_vals_966_, lean_object* v_heq_967_, lean_object* v_i_968_, lean_object* v_k_969_){
_start:
{
uint8_t v_res_970_; lean_object* v_r_971_; 
v_res_970_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4(v_00_u03b2_964_, v_keys_965_, v_vals_966_, v_heq_967_, v_i_968_, v_k_969_);
lean_dec_ref(v_k_969_);
lean_dec_ref(v_vals_966_);
lean_dec_ref(v_keys_965_);
v_r_971_ = lean_box(v_res_970_);
return v_r_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_972_, lean_object* v_n_973_, lean_object* v_k_974_, lean_object* v_v_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7___redArg(v_n_973_, v_k_974_, v_v_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_977_, size_t v_depth_978_, lean_object* v_keys_979_, lean_object* v_vals_980_, lean_object* v_heq_981_, lean_object* v_i_982_, lean_object* v_entries_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_depth_978_, v_keys_979_, v_vals_980_, v_i_982_, v_entries_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_985_, lean_object* v_depth_986_, lean_object* v_keys_987_, lean_object* v_vals_988_, lean_object* v_heq_989_, lean_object* v_i_990_, lean_object* v_entries_991_){
_start:
{
size_t v_depth_boxed_992_; lean_object* v_res_993_; 
v_depth_boxed_992_ = lean_unbox_usize(v_depth_986_);
lean_dec(v_depth_986_);
v_res_993_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(v_00_u03b2_985_, v_depth_boxed_992_, v_keys_987_, v_vals_988_, v_heq_989_, v_i_990_, v_entries_991_);
lean_dec_ref(v_vals_988_);
lean_dec_ref(v_keys_987_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8(lean_object* v_00_u03b2_994_, lean_object* v_x_995_, lean_object* v_x_996_, lean_object* v_x_997_, lean_object* v_x_998_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8___redArg(v_x_995_, v_x_996_, v_x_997_, v_x_998_);
return v___x_999_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_wrapRpcProcedure___redArg___lam__0(uint64_t v_x_1000_, uint64_t v_y_1001_){
_start:
{
uint8_t v___x_1002_; 
v___x_1002_ = lean_uint64_dec_lt(v_x_1000_, v_y_1001_);
if (v___x_1002_ == 0)
{
uint8_t v___x_1003_; 
v___x_1003_ = lean_uint64_dec_eq(v_x_1000_, v_y_1001_);
if (v___x_1003_ == 0)
{
uint8_t v___x_1004_; 
v___x_1004_ = 2;
return v___x_1004_;
}
else
{
uint8_t v___x_1005_; 
v___x_1005_ = 1;
return v___x_1005_;
}
}
else
{
uint8_t v___x_1006_; 
v___x_1006_ = 0;
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__0___boxed(lean_object* v_x_1007_, lean_object* v_y_1008_){
_start:
{
uint64_t v_x_boxed_1009_; uint64_t v_y_boxed_1010_; uint8_t v_res_1011_; lean_object* v_r_1012_; 
v_x_boxed_1009_ = lean_unbox_uint64(v_x_1007_);
lean_dec_ref(v_x_1007_);
v_y_boxed_1010_ = lean_unbox_uint64(v_y_1008_);
lean_dec_ref(v_y_1008_);
v_res_1011_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__0(v_x_boxed_1009_, v_y_boxed_1010_);
v_r_1012_ = lean_box(v_res_1011_);
return v_r_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__1(lean_object* v_expireTime_1013_, lean_object* v_x_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v_x_1014_);
lean_ctor_set(v___x_1015_, 1, v_expireTime_1013_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__2(lean_object* v_val_1017_, lean_object* v_inst_1018_, lean_object* v_x_1019_, lean_object* v___y_1020_){
_start:
{
if (lean_obj_tag(v_x_1019_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec_ref(v_inst_1018_);
v_a_1022_ = lean_ctor_get(v_x_1019_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_x_1019_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v_x_1019_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v_x_1019_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set_tag(v___x_1024_, 1);
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1048_; 
v_a_1030_ = lean_ctor_get(v_x_1019_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_x_1019_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1032_ = v_x_1019_;
v_isShared_1033_ = v_isSharedCheck_1048_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v_x_1019_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1048_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; lean_object* v_rpcEncode_1035_; lean_object* v_objects_1036_; lean_object* v_expireTime_1037_; lean_object* v___f_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v_fst_1042_; lean_object* v_snd_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1034_ = lean_st_ref_take(v_val_1017_);
v_rpcEncode_1035_ = lean_ctor_get(v_inst_1018_, 0);
lean_inc_ref(v_rpcEncode_1035_);
lean_dec_ref(v_inst_1018_);
v_objects_1036_ = lean_ctor_get(v___x_1034_, 0);
lean_inc_ref(v_objects_1036_);
v_expireTime_1037_ = lean_ctor_get(v___x_1034_, 1);
lean_inc(v_expireTime_1037_);
lean_dec(v___x_1034_);
v___f_1038_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1038_, 0, v_expireTime_1037_);
v___x_1039_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__2___closed__0));
v___x_1040_ = lean_apply_2(v_rpcEncode_1035_, v_a_1030_, v_objects_1036_);
v___x_1041_ = l_Prod_map___redArg(v___x_1039_, v___f_1038_, v___x_1040_);
v_fst_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_fst_1042_);
v_snd_1043_ = lean_ctor_get(v___x_1041_, 1);
lean_inc(v_snd_1043_);
lean_dec_ref(v___x_1041_);
v___x_1044_ = lean_st_ref_set(v_val_1017_, v_snd_1043_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set_tag(v___x_1032_, 0);
lean_ctor_set(v___x_1032_, 0, v_fst_1042_);
v___x_1046_ = v___x_1032_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_fst_1042_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__2___boxed(lean_object* v_val_1049_, lean_object* v_inst_1050_, lean_object* v_x_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__2(v_val_1049_, v_inst_1050_, v_x_1051_, v___y_1052_);
lean_dec_ref(v___y_1052_);
lean_dec(v_val_1049_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__3(lean_object* v___f_1062_, lean_object* v_inst_1063_, lean_object* v_method_1064_, lean_object* v_handler_1065_, lean_object* v_inst_1066_, uint64_t v_seshId_1067_, lean_object* v_j_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_rpcSessions_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v_rpcSessions_1071_ = lean_ctor_get(v___y_1069_, 0);
v___x_1072_ = lean_box_uint64(v_seshId_1067_);
lean_inc(v_rpcSessions_1071_);
v___x_1073_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_1062_, v_rpcSessions_1071_, v___x_1072_);
if (lean_obj_tag(v___x_1073_) == 1)
{
lean_object* v_val_1074_; lean_object* v___x_1075_; lean_object* v_rpcDecode_1076_; lean_object* v_objects_1077_; lean_object* v___x_1078_; 
v_val_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_val_1074_);
lean_dec_ref(v___x_1073_);
v___x_1075_ = lean_st_ref_get(v_val_1074_);
v_rpcDecode_1076_ = lean_ctor_get(v_inst_1063_, 1);
lean_inc_ref(v_rpcDecode_1076_);
lean_dec_ref(v_inst_1063_);
v_objects_1077_ = lean_ctor_get(v___x_1075_, 0);
lean_inc_ref(v_objects_1077_);
lean_dec(v___x_1075_);
lean_inc(v_j_1068_);
v___x_1078_ = lean_apply_2(v_rpcDecode_1076_, v_j_1068_, v_objects_1077_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1099_; 
lean_dec(v_val_1074_);
lean_dec_ref(v_inst_1066_);
lean_dec_ref(v_handler_1065_);
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1099_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1099_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
uint8_t v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1083_ = 3;
v___x_1084_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__0));
v___x_1085_ = 1;
v___x_1086_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_1064_, v___x_1085_);
v___x_1087_ = lean_string_append(v___x_1084_, v___x_1086_);
lean_dec_ref(v___x_1086_);
v___x_1088_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__1));
v___x_1089_ = lean_string_append(v___x_1087_, v___x_1088_);
v___x_1090_ = l_Lean_Json_compress(v_j_1068_);
v___x_1091_ = lean_string_append(v___x_1089_, v___x_1090_);
lean_dec_ref(v___x_1090_);
v___x_1092_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__2));
v___x_1093_ = lean_string_append(v___x_1091_, v___x_1092_);
v___x_1094_ = lean_string_append(v___x_1093_, v_a_1079_);
lean_dec(v_a_1079_);
v___x_1095_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*1, v___x_1083_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set_tag(v___x_1081_, 1);
lean_ctor_set(v___x_1081_, 0, v___x_1095_);
v___x_1097_ = v___x_1081_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1101_; 
lean_dec(v_j_1068_);
lean_dec(v_method_1064_);
v_a_1100_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1100_);
lean_dec_ref(v___x_1078_);
lean_inc_ref(v___y_1069_);
v___x_1101_ = lean_apply_3(v_handler_1065_, v_a_1100_, v___y_1069_, lean_box(0));
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___f_1103_; lean_object* v___x_1104_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref(v___x_1101_);
v___f_1103_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_1103_, 0, v_val_1074_);
lean_closure_set(v___f_1103_, 1, v_inst_1066_);
v___x_1104_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_a_1102_, v___f_1103_, v___y_1069_);
return v___x_1104_;
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec(v_val_1074_);
lean_dec_ref(v_inst_1066_);
v_a_1105_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1101_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1101_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_dec(v___x_1073_);
lean_dec(v_j_1068_);
lean_dec_ref(v_inst_1066_);
lean_dec_ref(v_handler_1065_);
lean_dec(v_method_1064_);
lean_dec_ref(v_inst_1063_);
v___x_1113_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__4));
v___x_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
return v___x_1114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__3___boxed(lean_object* v___f_1115_, lean_object* v_inst_1116_, lean_object* v_method_1117_, lean_object* v_handler_1118_, lean_object* v_inst_1119_, lean_object* v_seshId_1120_, lean_object* v_j_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
uint64_t v_seshId_boxed_1124_; lean_object* v_res_1125_; 
v_seshId_boxed_1124_ = lean_unbox_uint64(v_seshId_1120_);
lean_dec_ref(v_seshId_1120_);
v_res_1125_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__3(v___f_1115_, v_inst_1116_, v_method_1117_, v_handler_1118_, v_inst_1119_, v_seshId_boxed_1124_, v_j_1121_, v___y_1122_);
lean_dec_ref(v___y_1122_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg(lean_object* v_method_1127_, lean_object* v_inst_1128_, lean_object* v_inst_1129_, lean_object* v_handler_1130_){
_start:
{
lean_object* v___f_1131_; lean_object* v___f_1132_; 
v___f_1131_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___closed__0));
v___f_1132_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___boxed), 9, 5);
lean_closure_set(v___f_1132_, 0, v___f_1131_);
lean_closure_set(v___f_1132_, 1, v_inst_1128_);
lean_closure_set(v___f_1132_, 2, v_method_1127_);
lean_closure_set(v___f_1132_, 3, v_handler_1130_);
lean_closure_set(v___f_1132_, 4, v_inst_1129_);
return v___f_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure(lean_object* v_method_1133_, lean_object* v_paramType_1134_, lean_object* v_respType_1135_, lean_object* v_inst_1136_, lean_object* v_inst_1137_, lean_object* v_handler_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_Server_wrapRpcProcedure___redArg(v_method_1133_, v_inst_1136_, v_inst_1137_, v_handler_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg(lean_object* v_method_1146_, lean_object* v_inst_1147_, lean_object* v_inst_1148_, lean_object* v_handler_1149_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_initializing();
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1187_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1154_ = v___x_1151_;
v_isShared_1155_ = v_isSharedCheck_1187_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1187_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; uint8_t v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v_errMsg_1161_; uint8_t v___x_1162_; 
v___x_1156_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__0));
v___x_1157_ = 1;
lean_inc(v_method_1146_);
v___x_1158_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_1146_, v___x_1157_);
v___x_1159_ = lean_string_append(v___x_1156_, v___x_1158_);
lean_dec_ref(v___x_1158_);
v___x_1160_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__1));
v_errMsg_1161_ = lean_string_append(v___x_1159_, v___x_1160_);
v___x_1162_ = lean_unbox(v_a_1152_);
lean_dec(v_a_1152_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
lean_dec_ref(v_handler_1149_);
lean_dec_ref(v_inst_1148_);
lean_dec_ref(v_inst_1147_);
lean_dec(v_method_1146_);
v___x_1163_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__2));
v___x_1164_ = lean_string_append(v_errMsg_1161_, v___x_1163_);
v___x_1165_ = lean_mk_io_user_error(v___x_1164_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set_tag(v___x_1154_, 1);
lean_ctor_set(v___x_1154_, 0, v___x_1165_);
v___x_1167_ = v___x_1154_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
else
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1169_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_1170_ = lean_st_ref_get(v___x_1169_);
v___x_1171_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__3));
v___x_1172_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__4));
lean_inc(v_method_1146_);
v___x_1173_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1171_, v___x_1172_, v___x_1170_, v_method_1146_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
lean_dec_ref(v_errMsg_1161_);
v___x_1174_ = lean_st_ref_take(v___x_1169_);
lean_inc(v_method_1146_);
v___x_1175_ = l_Lean_Server_wrapRpcProcedure___redArg(v_method_1146_, v_inst_1147_, v_inst_1148_, v_handler_1149_);
v___x_1176_ = l_Lean_PersistentHashMap_insert___redArg(v___x_1171_, v___x_1172_, v___x_1174_, v_method_1146_, v___x_1175_);
v___x_1177_ = lean_st_ref_set(v___x_1169_, v___x_1176_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1177_);
v___x_1179_ = v___x_1154_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
else
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; 
lean_dec_ref(v_handler_1149_);
lean_dec_ref(v_inst_1148_);
lean_dec_ref(v_inst_1147_);
lean_dec(v_method_1146_);
v___x_1181_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__5));
v___x_1182_ = lean_string_append(v_errMsg_1161_, v___x_1181_);
v___x_1183_ = lean_mk_io_user_error(v___x_1182_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set_tag(v___x_1154_, 1);
lean_ctor_set(v___x_1154_, 0, v___x_1183_);
v___x_1185_ = v___x_1154_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
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
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec_ref(v_handler_1149_);
lean_dec_ref(v_inst_1148_);
lean_dec_ref(v_inst_1147_);
lean_dec(v_method_1146_);
v_a_1188_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1151_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1151_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg___boxed(lean_object* v_method_1196_, lean_object* v_inst_1197_, lean_object* v_inst_1198_, lean_object* v_handler_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_Server_registerBuiltinRpcProcedure___redArg(v_method_1196_, v_inst_1197_, v_inst_1198_, v_handler_1199_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure(lean_object* v_method_1202_, lean_object* v_paramType_1203_, lean_object* v_respType_1204_, lean_object* v_inst_1205_, lean_object* v_inst_1206_, lean_object* v_handler_1207_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_Server_registerBuiltinRpcProcedure___redArg(v_method_1202_, v_inst_1205_, v_inst_1206_, v_handler_1207_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___boxed(lean_object* v_method_1210_, lean_object* v_paramType_1211_, lean_object* v_respType_1212_, lean_object* v_inst_1213_, lean_object* v_inst_1214_, lean_object* v_handler_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_Server_registerBuiltinRpcProcedure(v_method_1210_, v_paramType_1211_, v_respType_1212_, v_inst_1213_, v_inst_1214_, v_handler_1215_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(lean_object* v_e_1218_, lean_object* v___y_1219_){
_start:
{
uint8_t v___x_1221_; 
v___x_1221_ = l_Lean_Expr_hasMVar(v_e_1218_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; 
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v_e_1218_);
return v___x_1222_;
}
else
{
lean_object* v___x_1223_; lean_object* v_mctx_1224_; lean_object* v___x_1225_; lean_object* v_fst_1226_; lean_object* v_snd_1227_; lean_object* v___x_1228_; lean_object* v_cache_1229_; lean_object* v_zetaDeltaFVarIds_1230_; lean_object* v_postponed_1231_; lean_object* v_diag_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1241_; 
v___x_1223_ = lean_st_ref_get(v___y_1219_);
v_mctx_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc_ref(v_mctx_1224_);
lean_dec(v___x_1223_);
v___x_1225_ = l_Lean_instantiateMVarsCore(v_mctx_1224_, v_e_1218_);
v_fst_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_fst_1226_);
v_snd_1227_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_snd_1227_);
lean_dec_ref(v___x_1225_);
v___x_1228_ = lean_st_ref_take(v___y_1219_);
v_cache_1229_ = lean_ctor_get(v___x_1228_, 1);
v_zetaDeltaFVarIds_1230_ = lean_ctor_get(v___x_1228_, 2);
v_postponed_1231_ = lean_ctor_get(v___x_1228_, 3);
v_diag_1232_ = lean_ctor_get(v___x_1228_, 4);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1241_ == 0)
{
lean_object* v_unused_1242_; 
v_unused_1242_ = lean_ctor_get(v___x_1228_, 0);
lean_dec(v_unused_1242_);
v___x_1234_ = v___x_1228_;
v_isShared_1235_ = v_isSharedCheck_1241_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_diag_1232_);
lean_inc(v_postponed_1231_);
lean_inc(v_zetaDeltaFVarIds_1230_);
lean_inc(v_cache_1229_);
lean_dec(v___x_1228_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1241_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v_snd_1227_);
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_snd_1227_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_cache_1229_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_zetaDeltaFVarIds_1230_);
lean_ctor_set(v_reuseFailAlloc_1240_, 3, v_postponed_1231_);
lean_ctor_set(v_reuseFailAlloc_1240_, 4, v_diag_1232_);
v___x_1237_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = lean_st_ref_set(v___y_1219_, v___x_1237_);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v_fst_1226_);
return v___x_1239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg___boxed(lean_object* v_e_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(v_e_1243_, v___y_1244_);
lean_dec(v___y_1244_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0(lean_object* v_e_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(v_e_1247_, v___y_1251_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___boxed(lean_object* v_e_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0(v_e_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg(lean_object* v_a_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg___boxed(lean_object* v_a_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg(v_a_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1(lean_object* v_00_u03b1_1283_, lean_object* v_a_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___boxed(lean_object* v_00_u03b1_1293_, lean_object* v_a_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1(v_00_u03b1_1293_, v_a_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
return v_res_1302_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1303_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0);
v___x_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
return v___x_1305_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1);
v___x_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(lean_object* v_env_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v___x_1311_; lean_object* v_nextMacroScope_1312_; lean_object* v_ngen_1313_; lean_object* v_auxDeclNGen_1314_; lean_object* v_traceState_1315_; lean_object* v_messages_1316_; lean_object* v_infoState_1317_; lean_object* v_snapshotTasks_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1329_; 
v___x_1311_ = lean_st_ref_take(v___y_1309_);
v_nextMacroScope_1312_ = lean_ctor_get(v___x_1311_, 1);
v_ngen_1313_ = lean_ctor_get(v___x_1311_, 2);
v_auxDeclNGen_1314_ = lean_ctor_get(v___x_1311_, 3);
v_traceState_1315_ = lean_ctor_get(v___x_1311_, 4);
v_messages_1316_ = lean_ctor_get(v___x_1311_, 6);
v_infoState_1317_ = lean_ctor_get(v___x_1311_, 7);
v_snapshotTasks_1318_ = lean_ctor_get(v___x_1311_, 8);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; lean_object* v_unused_1331_; 
v_unused_1330_ = lean_ctor_get(v___x_1311_, 5);
lean_dec(v_unused_1330_);
v_unused_1331_ = lean_ctor_get(v___x_1311_, 0);
lean_dec(v_unused_1331_);
v___x_1320_ = v___x_1311_;
v_isShared_1321_ = v_isSharedCheck_1329_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_snapshotTasks_1318_);
lean_inc(v_infoState_1317_);
lean_inc(v_messages_1316_);
lean_inc(v_traceState_1315_);
lean_inc(v_auxDeclNGen_1314_);
lean_inc(v_ngen_1313_);
lean_inc(v_nextMacroScope_1312_);
lean_dec(v___x_1311_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1329_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1322_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__2);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 5, v___x_1322_);
lean_ctor_set(v___x_1320_, 0, v_env_1308_);
v___x_1324_ = v___x_1320_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_env_1308_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_nextMacroScope_1312_);
lean_ctor_set(v_reuseFailAlloc_1328_, 2, v_ngen_1313_);
lean_ctor_set(v_reuseFailAlloc_1328_, 3, v_auxDeclNGen_1314_);
lean_ctor_set(v_reuseFailAlloc_1328_, 4, v_traceState_1315_);
lean_ctor_set(v_reuseFailAlloc_1328_, 5, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1328_, 6, v_messages_1316_);
lean_ctor_set(v_reuseFailAlloc_1328_, 7, v_infoState_1317_);
lean_ctor_set(v_reuseFailAlloc_1328_, 8, v_snapshotTasks_1318_);
v___x_1324_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1325_ = lean_st_ref_set(v___y_1309_, v___x_1324_);
v___x_1326_ = lean_box(0);
v___x_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
return v___x_1327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___boxed(lean_object* v_env_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(v_env_1332_, v___y_1333_);
lean_dec(v___y_1333_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2(lean_object* v_env_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(v_env_1336_, v___y_1338_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___boxed(lean_object* v_env_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2(v_env_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
return v_res_1345_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_registerRpcProcedure___lam__0(lean_object* v_x_1346_){
_start:
{
uint8_t v___x_1347_; 
v___x_1347_ = 0;
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__0___boxed(lean_object* v_x_1348_){
_start:
{
uint8_t v_res_1349_; lean_object* v_r_1350_; 
v_res_1349_ = l_Lean_Server_registerRpcProcedure___lam__0(v_x_1348_);
lean_dec(v_x_1348_);
v_r_1350_ = lean_box(v_res_1349_);
return v_r_1350_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__3));
v___x_1356_ = l_String_toRawSubstring_x27(v___x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__1(uint8_t v___x_1367_, lean_object* v___x_1368_, lean_object* v___x_1369_, lean_object* v_method_1370_, lean_object* v___x_1371_, uint8_t v___x_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_ref_1380_; lean_object* v_quotContext_1381_; lean_object* v_currMacroScope_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___y_1399_; lean_object* v___x_1412_; 
v_ref_1380_ = lean_ctor_get(v___y_1377_, 5);
v_quotContext_1381_ = lean_ctor_get(v___y_1377_, 10);
v_currMacroScope_1382_ = lean_ctor_get(v___y_1377_, 11);
v___x_1383_ = l_Lean_SourceInfo_fromRef(v_ref_1380_, v___x_1367_);
v___x_1384_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__0));
v___x_1385_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__1));
v___x_1386_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__2));
lean_inc_ref_n(v___x_1368_, 2);
v___x_1387_ = l_Lean_Name_mkStr4(v___x_1368_, v___x_1384_, v___x_1385_, v___x_1386_);
v___x_1388_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__3));
v___x_1389_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___lam__1___closed__4, &l_Lean_Server_registerRpcProcedure___lam__1___closed__4_once, _init_l_Lean_Server_registerRpcProcedure___lam__1___closed__4);
v___x_1390_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__5));
lean_inc(v_currMacroScope_1382_);
lean_inc(v_quotContext_1381_);
v___x_1391_ = l_Lean_addMacroScope(v_quotContext_1381_, v___x_1390_, v_currMacroScope_1382_);
v___x_1392_ = l_Lean_Name_mkStr3(v___x_1368_, v___x_1369_, v___x_1388_);
v___x_1393_ = lean_box(0);
v___x_1394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1392_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v___x_1395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
lean_ctor_set(v___x_1395_, 1, v___x_1393_);
lean_inc(v___x_1383_);
v___x_1396_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1383_);
lean_ctor_set(v___x_1396_, 1, v___x_1389_);
lean_ctor_set(v___x_1396_, 2, v___x_1391_);
lean_ctor_set(v___x_1396_, 3, v___x_1395_);
v___x_1397_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__7));
lean_inc(v_method_1370_);
v___x_1412_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_1393_, v_method_1370_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v___x_1413_; 
lean_inc(v_method_1370_);
v___x_1413_ = l_Lean_quoteNameMk(v_method_1370_);
v___y_1399_ = v___x_1413_;
goto v___jp_1398_;
}
else
{
lean_object* v_val_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v_val_1414_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_val_1414_);
lean_dec_ref(v___x_1412_);
v___x_1415_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__10));
lean_inc_ref(v___x_1368_);
v___x_1416_ = l_Lean_Name_mkStr4(v___x_1368_, v___x_1384_, v___x_1385_, v___x_1415_);
v___x_1417_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__11));
v___x_1418_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__12));
v___x_1419_ = lean_string_intercalate(v___x_1418_, v_val_1414_);
v___x_1420_ = lean_string_append(v___x_1417_, v___x_1419_);
lean_dec_ref(v___x_1419_);
v___x_1421_ = lean_box(2);
v___x_1422_ = l_Lean_Syntax_mkNameLit(v___x_1420_, v___x_1421_);
v___x_1423_ = lean_unsigned_to_nat(1u);
v___x_1424_ = lean_mk_empty_array_with_capacity(v___x_1423_);
v___x_1425_ = lean_array_push(v___x_1424_, v___x_1422_);
v___x_1426_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1421_);
lean_ctor_set(v___x_1426_, 1, v___x_1416_);
lean_ctor_set(v___x_1426_, 2, v___x_1425_);
v___y_1399_ = v___x_1426_;
goto v___jp_1398_;
}
v___jp_1398_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1400_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__8));
v___x_1401_ = l_Lean_Name_mkStr4(v___x_1368_, v___x_1384_, v___x_1385_, v___x_1400_);
v___x_1402_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__9));
lean_inc_n(v___x_1383_, 3);
v___x_1403_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1383_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
v___x_1404_ = l_Lean_Syntax_node1(v___x_1383_, v___x_1401_, v___x_1403_);
v___x_1405_ = lean_mk_syntax_ident(v_method_1370_);
lean_inc(v___x_1404_);
v___x_1406_ = l_Lean_Syntax_node4(v___x_1383_, v___x_1397_, v___y_1399_, v___x_1404_, v___x_1404_, v___x_1405_);
v___x_1407_ = l_Lean_Syntax_node2(v___x_1383_, v___x_1387_, v___x_1396_, v___x_1406_);
v___x_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1371_);
v___x_1409_ = l_Lean_Elab_Term_elabTerm(v___x_1407_, v___x_1408_, v___x_1372_, v___x_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
lean_dec_ref(v___y_1377_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1411_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref(v___x_1409_);
v___x_1411_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(v_a_1410_, v___y_1376_);
return v___x_1411_;
}
else
{
return v___x_1409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__1___boxed(lean_object* v___x_1427_, lean_object* v___x_1428_, lean_object* v___x_1429_, lean_object* v_method_1430_, lean_object* v___x_1431_, lean_object* v___x_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
uint8_t v___x_6265__boxed_1440_; uint8_t v___x_6269__boxed_1441_; lean_object* v_res_1442_; 
v___x_6265__boxed_1440_ = lean_unbox(v___x_1427_);
v___x_6269__boxed_1441_ = lean_unbox(v___x_1432_);
v_res_1442_ = l_Lean_Server_registerRpcProcedure___lam__1(v___x_6265__boxed_1440_, v___x_1428_, v___x_1429_, v_method_1430_, v___x_1431_, v___x_6269__boxed_1441_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
lean_dec(v___y_1438_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
return v_res_1442_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1443_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0);
v___x_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
return v___x_1445_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1446_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1);
v___x_1447_ = lean_unsigned_to_nat(0u);
v___x_1448_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
lean_ctor_set(v___x_1448_, 2, v___x_1447_);
lean_ctor_set(v___x_1448_, 3, v___x_1447_);
lean_ctor_set(v___x_1448_, 4, v___x_1446_);
lean_ctor_set(v___x_1448_, 5, v___x_1446_);
lean_ctor_set(v___x_1448_, 6, v___x_1446_);
lean_ctor_set(v___x_1448_, 7, v___x_1446_);
lean_ctor_set(v___x_1448_, 8, v___x_1446_);
lean_ctor_set(v___x_1448_, 9, v___x_1446_);
return v___x_1448_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1449_ = lean_unsigned_to_nat(32u);
v___x_1450_ = lean_mk_empty_array_with_capacity(v___x_1449_);
v___x_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
return v___x_1451_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4(void){
_start:
{
size_t v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1452_ = ((size_t)5ULL);
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = lean_unsigned_to_nat(32u);
v___x_1455_ = lean_mk_empty_array_with_capacity(v___x_1454_);
v___x_1456_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3);
v___x_1457_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
lean_ctor_set(v___x_1457_, 1, v___x_1455_);
lean_ctor_set(v___x_1457_, 2, v___x_1453_);
lean_ctor_set(v___x_1457_, 3, v___x_1453_);
lean_ctor_set_usize(v___x_1457_, 4, v___x_1452_);
return v___x_1457_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__5(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1458_ = lean_box(1);
v___x_1459_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4);
v___x_1460_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1);
v___x_1461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
lean_ctor_set(v___x_1461_, 1, v___x_1459_);
lean_ctor_set(v___x_1461_, 2, v___x_1458_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3(lean_object* v_msgData_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v___x_1466_; lean_object* v_env_1467_; lean_object* v_options_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1466_ = lean_st_ref_get(v___y_1464_);
v_env_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc_ref(v_env_1467_);
lean_dec(v___x_1466_);
v_options_1468_ = lean_ctor_get(v___y_1463_, 2);
v___x_1469_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2);
v___x_1470_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__5);
lean_inc_ref(v_options_1468_);
v___x_1471_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1471_, 0, v_env_1467_);
lean_ctor_set(v___x_1471_, 1, v___x_1469_);
lean_ctor_set(v___x_1471_, 2, v___x_1470_);
lean_ctor_set(v___x_1471_, 3, v_options_1468_);
v___x_1472_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
lean_ctor_set(v___x_1472_, 1, v_msgData_1462_);
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___boxed(lean_object* v_msgData_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3(v_msgData_1474_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(lean_object* v_msg_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_ref_1483_; lean_object* v___x_1484_; lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1493_; 
v_ref_1483_ = lean_ctor_get(v___y_1480_, 5);
v___x_1484_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3(v_msg_1479_, v___y_1480_, v___y_1481_);
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1493_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1493_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; lean_object* v___x_1491_; 
lean_inc(v_ref_1483_);
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v_ref_1483_);
lean_ctor_set(v___x_1489_, 1, v_a_1485_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set_tag(v___x_1487_, 1);
lean_ctor_set(v___x_1487_, 0, v___x_1489_);
v___x_1491_ = v___x_1487_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg___boxed(lean_object* v_msg_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v_msg_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
return v_res_1498_;
}
}
static uint64_t _init_l_Lean_Server_registerRpcProcedure___closed__4(void){
_start:
{
lean_object* v___x_1516_; uint64_t v___x_1517_; 
v___x_1516_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__3));
v___x_1517_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1516_);
return v___x_1517_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__5(void){
_start:
{
uint64_t v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1518_ = lean_uint64_once(&l_Lean_Server_registerRpcProcedure___closed__4, &l_Lean_Server_registerRpcProcedure___closed__4_once, _init_l_Lean_Server_registerRpcProcedure___closed__4);
v___x_1519_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__3));
v___x_1520_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
lean_ctor_set_uint64(v___x_1520_, sizeof(void*)*1, v___x_1518_);
return v___x_1520_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__6(void){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1521_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__7(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__6, &l_Lean_Server_registerRpcProcedure___closed__6_once, _init_l_Lean_Server_registerRpcProcedure___closed__6);
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
return v___x_1523_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__8(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1524_ = lean_box(1);
v___x_1525_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4);
v___x_1526_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__7, &l_Lean_Server_registerRpcProcedure___closed__7_once, _init_l_Lean_Server_registerRpcProcedure___closed__7);
v___x_1527_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
lean_ctor_set(v___x_1527_, 1, v___x_1525_);
lean_ctor_set(v___x_1527_, 2, v___x_1524_);
return v___x_1527_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__9(void){
_start:
{
uint8_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1528_ = 1;
v___x_1529_ = lean_unsigned_to_nat(0u);
v___x_1530_ = lean_box(0);
v___x_1531_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__1));
v___x_1532_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__8, &l_Lean_Server_registerRpcProcedure___closed__8_once, _init_l_Lean_Server_registerRpcProcedure___closed__8);
v___x_1533_ = lean_box(1);
v___x_1534_ = 0;
v___x_1535_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__5, &l_Lean_Server_registerRpcProcedure___closed__5_once, _init_l_Lean_Server_registerRpcProcedure___closed__5);
v___x_1536_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
lean_ctor_set(v___x_1536_, 1, v___x_1533_);
lean_ctor_set(v___x_1536_, 2, v___x_1532_);
lean_ctor_set(v___x_1536_, 3, v___x_1531_);
lean_ctor_set(v___x_1536_, 4, v___x_1530_);
lean_ctor_set(v___x_1536_, 5, v___x_1529_);
lean_ctor_set(v___x_1536_, 6, v___x_1530_);
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*7, v___x_1534_);
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*7 + 1, v___x_1534_);
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*7 + 2, v___x_1534_);
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*7 + 3, v___x_1528_);
return v___x_1536_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__10(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1537_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__7, &l_Lean_Server_registerRpcProcedure___closed__7_once, _init_l_Lean_Server_registerRpcProcedure___closed__7);
v___x_1538_ = lean_unsigned_to_nat(0u);
v___x_1539_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
lean_ctor_set(v___x_1539_, 2, v___x_1538_);
lean_ctor_set(v___x_1539_, 3, v___x_1538_);
lean_ctor_set(v___x_1539_, 4, v___x_1537_);
lean_ctor_set(v___x_1539_, 5, v___x_1537_);
lean_ctor_set(v___x_1539_, 6, v___x_1537_);
lean_ctor_set(v___x_1539_, 7, v___x_1537_);
lean_ctor_set(v___x_1539_, 8, v___x_1537_);
lean_ctor_set(v___x_1539_, 9, v___x_1537_);
return v___x_1539_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__11(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__7, &l_Lean_Server_registerRpcProcedure___closed__7_once, _init_l_Lean_Server_registerRpcProcedure___closed__7);
v___x_1541_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
lean_ctor_set(v___x_1541_, 2, v___x_1540_);
lean_ctor_set(v___x_1541_, 3, v___x_1540_);
lean_ctor_set(v___x_1541_, 4, v___x_1540_);
lean_ctor_set(v___x_1541_, 5, v___x_1540_);
return v___x_1541_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__12(void){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__7, &l_Lean_Server_registerRpcProcedure___closed__7_once, _init_l_Lean_Server_registerRpcProcedure___closed__7);
v___x_1543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
lean_ctor_set(v___x_1543_, 2, v___x_1542_);
lean_ctor_set(v___x_1543_, 3, v___x_1542_);
lean_ctor_set(v___x_1543_, 4, v___x_1542_);
return v___x_1543_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__13(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1544_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__12, &l_Lean_Server_registerRpcProcedure___closed__12_once, _init_l_Lean_Server_registerRpcProcedure___closed__12);
v___x_1545_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4);
v___x_1546_ = lean_box(1);
v___x_1547_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__11, &l_Lean_Server_registerRpcProcedure___closed__11_once, _init_l_Lean_Server_registerRpcProcedure___closed__11);
v___x_1548_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__10, &l_Lean_Server_registerRpcProcedure___closed__10_once, _init_l_Lean_Server_registerRpcProcedure___closed__10);
v___x_1549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
lean_ctor_set(v___x_1549_, 1, v___x_1547_);
lean_ctor_set(v___x_1549_, 2, v___x_1546_);
lean_ctor_set(v___x_1549_, 3, v___x_1545_);
lean_ctor_set(v___x_1549_, 4, v___x_1544_);
return v___x_1549_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__14(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1550_ = lean_box(0);
v___x_1551_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1));
v___x_1552_ = l_Lean_mkConst(v___x_1551_, v___x_1550_);
return v___x_1552_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__18(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__7, &l_Lean_Server_registerRpcProcedure___closed__7_once, _init_l_Lean_Server_registerRpcProcedure___closed__7);
v___x_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
return v___x_1560_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__20(void){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__19));
v___x_1563_ = l_Lean_stringToMessageData(v___x_1562_);
return v___x_1563_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__21(void){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__1));
v___x_1565_ = l_Lean_stringToMessageData(v___x_1564_);
return v___x_1565_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__22(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__5));
v___x_1567_ = l_Lean_stringToMessageData(v___x_1566_);
return v___x_1567_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__24(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__23));
v___x_1570_ = l_Lean_stringToMessageData(v___x_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure(lean_object* v_method_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v_env_1578_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___y_1658_; lean_object* v___y_1659_; uint8_t v___x_1665_; 
v___x_1575_ = lean_st_ref_get(v_a_1573_);
v___x_1576_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_1577_ = lean_st_ref_get(v___x_1576_);
v_env_1578_ = lean_ctor_get(v___x_1575_, 0);
lean_inc_ref(v_env_1578_);
lean_dec(v___x_1575_);
v___x_1651_ = lean_box(0);
v___x_1652_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__20, &l_Lean_Server_registerRpcProcedure___closed__20_once, _init_l_Lean_Server_registerRpcProcedure___closed__20);
lean_inc(v_method_1571_);
v___x_1653_ = l_Lean_MessageData_ofName(v_method_1571_);
v___x_1654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1652_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__21, &l_Lean_Server_registerRpcProcedure___closed__21_once, _init_l_Lean_Server_registerRpcProcedure___closed__21);
v___x_1656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1654_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1665_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(v___x_1577_, v_method_1571_);
lean_dec(v___x_1577_);
if (v___x_1665_ == 0)
{
v___y_1658_ = v_a_1572_;
v___y_1659_ = v_a_1573_;
goto v___jp_1657_;
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
lean_dec_ref(v_env_1578_);
lean_dec(v_method_1571_);
v___x_1666_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__24, &l_Lean_Server_registerRpcProcedure___closed__24_once, _init_l_Lean_Server_registerRpcProcedure___closed__24);
v___x_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1656_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v___x_1667_, v_a_1572_, v_a_1573_);
return v___x_1668_;
}
v___jp_1579_:
{
lean_object* v___x_1582_; uint8_t v___x_1583_; uint8_t v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___f_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1582_ = lean_box(0);
v___x_1583_ = 1;
v___x_1584_ = 0;
v___x_1585_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__2));
v___x_1586_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__9, &l_Lean_Server_registerRpcProcedure___closed__9_once, _init_l_Lean_Server_registerRpcProcedure___closed__9);
v___x_1587_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__13, &l_Lean_Server_registerRpcProcedure___closed__13_once, _init_l_Lean_Server_registerRpcProcedure___closed__13);
v___x_1588_ = lean_st_mk_ref(v___x_1587_);
v___x_1589_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_1590_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_1591_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__14, &l_Lean_Server_registerRpcProcedure___closed__14_once, _init_l_Lean_Server_registerRpcProcedure___closed__14);
v___x_1592_ = lean_box(v___x_1584_);
v___x_1593_ = lean_box(v___x_1583_);
lean_inc(v_method_1571_);
v___f_1594_ = lean_alloc_closure((void*)(l_Lean_Server_registerRpcProcedure___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1594_, 0, v___x_1592_);
lean_closure_set(v___f_1594_, 1, v___x_1589_);
lean_closure_set(v___f_1594_, 2, v___x_1590_);
lean_closure_set(v___f_1594_, 3, v_method_1571_);
lean_closure_set(v___f_1594_, 4, v___x_1591_);
lean_closure_set(v___f_1594_, 5, v___x_1593_);
v___x_1595_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___boxed), 9, 2);
lean_closure_set(v___x_1595_, 0, lean_box(0));
lean_closure_set(v___x_1595_, 1, v___f_1594_);
v___x_1596_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__15));
v___x_1597_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_1595_, v___x_1585_, v___x_1596_, v___x_1586_, v___x_1588_, v___y_1580_, v___y_1581_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1599_; lean_object* v_fst_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1641_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1598_);
lean_dec_ref(v___x_1597_);
v___x_1599_ = lean_st_ref_get(v___x_1588_);
lean_dec(v___x_1588_);
lean_dec(v___x_1599_);
v_fst_1600_ = lean_ctor_get(v_a_1598_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_a_1598_);
if (v_isSharedCheck_1641_ == 0)
{
lean_object* v_unused_1642_; 
v_unused_1642_ = lean_ctor_get(v_a_1598_, 1);
lean_dec(v_unused_1642_);
v___x_1602_ = v_a_1598_;
v_isShared_1603_ = v_isSharedCheck_1641_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_fst_1600_);
lean_dec(v_a_1598_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1641_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; lean_object* v___x_1610_; 
v___x_1604_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__17));
lean_inc(v_method_1571_);
v___x_1605_ = l_Lean_Name_append(v_method_1571_, v___x_1604_);
lean_inc_n(v___x_1605_, 2);
v___x_1606_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
lean_ctor_set(v___x_1606_, 1, v___x_1582_);
lean_ctor_set(v___x_1606_, 2, v___x_1591_);
v___x_1607_ = lean_box(0);
v___x_1608_ = 1;
if (v_isShared_1603_ == 0)
{
lean_ctor_set_tag(v___x_1602_, 1);
lean_ctor_set(v___x_1602_, 1, v___x_1582_);
lean_ctor_set(v___x_1602_, 0, v___x_1605_);
v___x_1610_ = v___x_1602_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v___x_1582_);
v___x_1610_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1611_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1611_, 0, v___x_1606_);
lean_ctor_set(v___x_1611_, 1, v_fst_1600_);
lean_ctor_set(v___x_1611_, 2, v___x_1607_);
lean_ctor_set(v___x_1611_, 3, v___x_1610_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*4, v___x_1608_);
v___x_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
lean_inc_ref(v___x_1612_);
v___x_1613_ = l_Lean_addDecl(v___x_1612_, v___x_1584_, v___y_1580_, v___y_1581_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v___x_1614_; lean_object* v_env_1615_; lean_object* v_nextMacroScope_1616_; lean_object* v_ngen_1617_; lean_object* v_auxDeclNGen_1618_; lean_object* v_traceState_1619_; lean_object* v_messages_1620_; lean_object* v_infoState_1621_; lean_object* v_snapshotTasks_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1638_; 
lean_dec_ref(v___x_1613_);
v___x_1614_ = lean_st_ref_take(v___y_1581_);
v_env_1615_ = lean_ctor_get(v___x_1614_, 0);
v_nextMacroScope_1616_ = lean_ctor_get(v___x_1614_, 1);
v_ngen_1617_ = lean_ctor_get(v___x_1614_, 2);
v_auxDeclNGen_1618_ = lean_ctor_get(v___x_1614_, 3);
v_traceState_1619_ = lean_ctor_get(v___x_1614_, 4);
v_messages_1620_ = lean_ctor_get(v___x_1614_, 6);
v_infoState_1621_ = lean_ctor_get(v___x_1614_, 7);
v_snapshotTasks_1622_ = lean_ctor_get(v___x_1614_, 8);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1638_ == 0)
{
lean_object* v_unused_1639_; 
v_unused_1639_ = lean_ctor_get(v___x_1614_, 5);
lean_dec(v_unused_1639_);
v___x_1624_ = v___x_1614_;
v_isShared_1625_ = v_isSharedCheck_1638_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_snapshotTasks_1622_);
lean_inc(v_infoState_1621_);
lean_inc(v_messages_1620_);
lean_inc(v_traceState_1619_);
lean_inc(v_auxDeclNGen_1618_);
lean_inc(v_ngen_1617_);
lean_inc(v_nextMacroScope_1616_);
lean_inc(v_env_1615_);
lean_dec(v___x_1614_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1638_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; 
lean_inc(v___x_1605_);
v___x_1626_ = l_Lean_markMeta(v_env_1615_, v___x_1605_);
v___x_1627_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__18, &l_Lean_Server_registerRpcProcedure___closed__18_once, _init_l_Lean_Server_registerRpcProcedure___closed__18);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 5, v___x_1627_);
lean_ctor_set(v___x_1624_, 0, v___x_1626_);
v___x_1629_ = v___x_1624_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1626_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_nextMacroScope_1616_);
lean_ctor_set(v_reuseFailAlloc_1637_, 2, v_ngen_1617_);
lean_ctor_set(v_reuseFailAlloc_1637_, 3, v_auxDeclNGen_1618_);
lean_ctor_set(v_reuseFailAlloc_1637_, 4, v_traceState_1619_);
lean_ctor_set(v_reuseFailAlloc_1637_, 5, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1637_, 6, v_messages_1620_);
lean_ctor_set(v_reuseFailAlloc_1637_, 7, v_infoState_1621_);
lean_ctor_set(v_reuseFailAlloc_1637_, 8, v_snapshotTasks_1622_);
v___x_1629_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = lean_st_ref_set(v___y_1581_, v___x_1629_);
v___x_1631_ = l_Lean_compileDecl(v___x_1612_, v___x_1583_, v___y_1580_, v___y_1581_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v___x_1632_; lean_object* v_env_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_dec_ref(v___x_1631_);
v___x_1632_ = lean_st_ref_get(v___y_1581_);
v_env_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc_ref(v_env_1633_);
lean_dec(v___x_1632_);
v___x_1634_ = l_Lean_Server_userRpcProcedures;
v___x_1635_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1634_, v_env_1633_, v_method_1571_, v___x_1605_);
v___x_1636_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(v___x_1635_, v___y_1581_);
return v___x_1636_;
}
else
{
lean_dec(v___x_1605_);
lean_dec(v_method_1571_);
return v___x_1631_;
}
}
}
}
else
{
lean_dec_ref(v___x_1612_);
lean_dec(v___x_1605_);
lean_dec(v_method_1571_);
return v___x_1613_;
}
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec(v___x_1588_);
lean_dec(v_method_1571_);
v_a_1643_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1597_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1597_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
v___jp_1657_:
{
lean_object* v___x_1660_; uint8_t v___x_1661_; 
v___x_1660_ = l_Lean_Server_userRpcProcedures;
lean_inc(v_method_1571_);
v___x_1661_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_1651_, v___x_1660_, v_env_1578_, v_method_1571_);
if (v___x_1661_ == 0)
{
lean_dec_ref(v___x_1656_);
v___y_1580_ = v___y_1658_;
v___y_1581_ = v___y_1659_;
goto v___jp_1579_;
}
else
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
lean_dec(v_method_1571_);
v___x_1662_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__22, &l_Lean_Server_registerRpcProcedure___closed__22_once, _init_l_Lean_Server_registerRpcProcedure___closed__22);
v___x_1663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1656_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v___x_1663_, v___y_1658_, v___y_1659_);
return v___x_1664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___boxed(lean_object* v_method_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_Server_registerRpcProcedure(v_method_1669_, v_a_1670_, v_a_1671_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3(lean_object* v_00_u03b1_1674_, lean_object* v_msg_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v_msg_1675_, v___y_1676_, v___y_1677_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___boxed(lean_object* v_00_u03b1_1680_, lean_object* v_msg_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3(v_00_u03b1_1680_, v_msg_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(lean_object* v___x_1686_, lean_object* v_decl_1687_, lean_object* v_x_1688_, uint8_t v_attrKind_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v___x_1693_; 
lean_inc(v_decl_1687_);
v___x_1693_ = l_Lean_ensureAttrDeclIsMeta(v___x_1686_, v_decl_1687_, v_attrKind_1689_, v___y_1690_, v___y_1691_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v___x_1694_; 
lean_dec_ref(v___x_1693_);
v___x_1694_ = l_Lean_Server_registerRpcProcedure(v_decl_1687_, v___y_1690_, v___y_1691_);
return v___x_1694_;
}
else
{
lean_dec(v_decl_1687_);
return v___x_1693_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed(lean_object* v___x_1695_, lean_object* v_decl_1696_, lean_object* v_x_1697_, lean_object* v_attrKind_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
uint8_t v_attrKind_boxed_1702_; lean_object* v_res_1703_; 
v_attrKind_boxed_1702_ = lean_unbox(v_attrKind_1698_);
v_res_1703_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(v___x_1695_, v_decl_1696_, v_x_1697_, v_attrKind_boxed_1702_, v___y_1699_, v___y_1700_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v_x_1697_);
return v_res_1703_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_));
v___x_1706_ = l_Lean_stringToMessageData(v___x_1705_);
return v___x_1706_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_));
v___x_1709_ = l_Lean_stringToMessageData(v___x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(lean_object* v___x_1710_, lean_object* v_decl_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1715_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_);
v___x_1716_ = l_Lean_MessageData_ofName(v___x_1710_);
v___x_1717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1715_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_);
v___x_1719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1717_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
v___x_1720_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v___x_1719_, v___y_1712_, v___y_1713_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed(lean_object* v___x_1721_, lean_object* v_decl_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(v___x_1721_, v_decl_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v_decl_1722_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__31_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_));
v___x_1807_ = l_Lean_registerBuiltinAttribute(v___x_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed(lean_object* v_a_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_();
return v_res_1809_;
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
