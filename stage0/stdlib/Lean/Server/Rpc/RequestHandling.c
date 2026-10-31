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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Prod_map___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson(lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
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
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_Lean_Server_RequestM_asTask___redArg(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Server_instInhabitedRequestError_default;
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Server_requestHandlers;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value;
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Server_handleRpcCall___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_handleRpcCall___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Failed to evaluate RPC constant '"};
static const lean_object* l_Lean_Server_handleRpcCall___lam__3___closed__0 = (const lean_object*)&l_Lean_Server_handleRpcCall___lam__3___closed__0_value;
static const lean_string_object l_Lean_Server_handleRpcCall___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "': "};
static const lean_object* l_Lean_Server_handleRpcCall___lam__3___closed__1 = (const lean_object*)&l_Lean_Server_handleRpcCall___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__3(lean_object*, lean_object*, uint8_t, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__0_value;
static const lean_string_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Failed to register LSP request handler for '"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__1 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__1_value;
static const lean_string_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "': only possible during initialization"};
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
static const lean_closure_object l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__0 = (const lean_object*)&l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__0_value;
static const lean_closure_object l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__1 = (const lean_object*)&l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__1_value;
static const lean_string_object l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Failed to register builtin RPC call handler for '"};
static const lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__2 = (const lean_object*)&l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__2_value;
static const lean_string_object l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__3 = (const lean_object*)&l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__3_value;
static const lean_string_object l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = ": only possible during initialization"};
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
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Server_registerRpcProcedure_spec__2_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Server_registerRpcProcedure_spec__2_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Server_registerRpcProcedure_spec__2_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Server_registerRpcProcedure_spec__2_spec__2___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_registerRpcProcedure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerRpcProcedure___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerRpcProcedure___closed__0 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___closed__0_value;
static const lean_string_object l_Lean_Server_registerRpcProcedure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "_rpc_wrapped"};
static const lean_object* l_Lean_Server_registerRpcProcedure___closed__1 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___closed__1_value;
static const lean_ctor_object l_Lean_Server_registerRpcProcedure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_registerRpcProcedure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 241, 252, 252, 247, 5, 133, 205)}};
static const lean_object* l_Lean_Server_registerRpcProcedure___closed__2 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___closed__2_value;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__3;
static const lean_array_object l_Lean_Server_registerRpcProcedure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_registerRpcProcedure___closed__4 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___closed__4_value;
static const lean_ctor_object l_Lean_Server_registerRpcProcedure___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 16, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_registerRpcProcedure___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_registerRpcProcedure___closed__4_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_registerRpcProcedure___closed__5 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___closed__5_value;
static const lean_ctor_object l_Lean_Server_registerRpcProcedure___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Server_registerRpcProcedure___closed__6 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___closed__6_value;
static const lean_ctor_object l_Lean_Server_registerRpcProcedure___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_registerRpcProcedure___closed__7 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___closed__7_value;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Server_registerRpcProcedure___closed__8;
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
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__15;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__16;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__17;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Server_registerRpcProcedure_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Server_registerRpcProcedure_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Server_registerRpcProcedure_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_16_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_49_; lean_object* v_fst_50_; uint8_t v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_49_ = lean_array_uget_borrowed(v_as_39_, v_i_40_);
v_fst_50_ = lean_ctor_get(v___x_49_, 0);
v___x_51_ = 1;
lean_inc_ref(v_env_38_);
v___x_52_ = l_Lean_Environment_setExporting(v_env_38_, v___x_51_);
lean_inc(v_fst_50_);
v___x_53_ = l_Lean_Environment_contains(v___x_52_, v_fst_50_, v___x_48_);
if (v___x_53_ == 0)
{
v___y_44_ = v_b_42_;
goto v___jp_43_;
}
else
{
lean_object* v___x_54_; 
lean_inc(v___x_49_);
v___x_54_ = lean_array_push(v_b_42_, v___x_49_);
v___y_44_ = v___x_54_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_55_, lean_object* v_as_56_, lean_object* v_i_57_, lean_object* v_stop_58_, lean_object* v_b_59_){
_start:
{
size_t v_i_boxed_60_; size_t v_stop_boxed_61_; lean_object* v_res_62_; 
v_i_boxed_60_ = lean_unbox_usize(v_i_57_);
lean_dec(v_i_57_);
v_stop_boxed_61_ = lean_unbox_usize(v_stop_58_);
lean_dec(v_stop_58_);
v_res_62_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1(v_env_55_, v_as_56_, v_i_boxed_60_, v_stop_boxed_61_, v_b_59_);
lean_dec_ref(v_as_56_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__2(lean_object* v_env_63_, lean_object* v_as_64_, size_t v_i_65_, size_t v_stop_66_, lean_object* v_b_67_){
_start:
{
lean_object* v___y_69_; uint8_t v___x_73_; 
v___x_73_ = lean_usize_dec_eq(v_i_65_, v_stop_66_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; lean_object* v_fst_75_; uint8_t v___x_76_; 
v___x_74_ = lean_array_uget_borrowed(v_as_64_, v_i_65_);
v_fst_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_fst_75_);
lean_inc_ref(v_env_63_);
v___x_76_ = l_Lean_Environment_contains(v_env_63_, v_fst_75_, v___x_73_);
if (v___x_76_ == 0)
{
v___y_69_ = v_b_67_;
goto v___jp_68_;
}
else
{
lean_object* v___x_77_; 
lean_inc(v___x_74_);
v___x_77_ = lean_array_push(v_b_67_, v___x_74_);
v___y_69_ = v___x_77_;
goto v___jp_68_;
}
}
else
{
lean_dec_ref(v_env_63_);
return v_b_67_;
}
v___jp_68_:
{
size_t v___x_70_; size_t v___x_71_; 
v___x_70_ = ((size_t)1ULL);
v___x_71_ = lean_usize_add(v_i_65_, v___x_70_);
v_i_65_ = v___x_71_;
v_b_67_ = v___y_69_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_78_, lean_object* v_as_79_, lean_object* v_i_80_, lean_object* v_stop_81_, lean_object* v_b_82_){
_start:
{
size_t v_i_boxed_83_; size_t v_stop_boxed_84_; lean_object* v_res_85_; 
v_i_boxed_83_ = lean_unbox_usize(v_i_80_);
lean_dec(v_i_80_);
v_stop_boxed_84_ = lean_unbox_usize(v_stop_81_);
lean_dec(v_stop_81_);
v_res_85_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__2(v_env_78_, v_as_79_, v_i_boxed_83_, v_stop_boxed_84_, v_b_82_);
lean_dec_ref(v_as_79_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_(lean_object* v_env_90_, lean_object* v_s_91_){
_start:
{
lean_object* v___x_92_; lean_object* v___y_94_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_103_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_104_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0(v___x_103_, v_s_91_);
v___x_105_ = lean_array_get_size(v___x_104_);
v___x_106_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_107_ = lean_nat_dec_lt(v___x_92_, v___x_105_);
if (v___x_107_ == 0)
{
lean_dec_ref(v___x_104_);
v___y_94_ = v___x_106_;
goto v___jp_93_;
}
else
{
size_t v___x_108_; size_t v___x_109_; lean_object* v___x_110_; 
v___x_108_ = ((size_t)0ULL);
v___x_109_ = lean_usize_of_nat(v___x_105_);
lean_inc_ref(v_env_90_);
v___x_110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__2(v_env_90_, v___x_104_, v___x_108_, v___x_109_, v___x_106_);
lean_dec_ref(v___x_104_);
v___y_94_ = v___x_110_;
goto v___jp_93_;
}
v___jp_93_:
{
lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_95_ = lean_array_get_size(v___y_94_);
v___x_96_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_97_ = lean_nat_dec_lt(v___x_92_, v___x_95_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; 
lean_dec_ref(v_env_90_);
v___x_98_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_98_, 0, v___x_96_);
lean_ctor_set(v___x_98_, 1, v___x_96_);
lean_ctor_set(v___x_98_, 2, v___y_94_);
return v___x_98_;
}
else
{
size_t v___x_99_; size_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_99_ = ((size_t)0ULL);
v___x_100_ = lean_usize_of_nat(v___x_95_);
v___x_101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1(v_env_90_, v___y_94_, v___x_99_, v___x_100_, v___x_96_);
lean_inc_ref(v___x_101_);
v___x_102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
lean_ctor_set(v___x_102_, 2, v___y_94_);
return v___x_102_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2____boxed(lean_object* v_env_111_, lean_object* v_s_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_(v_env_111_, v_s_112_);
lean_dec(v_s_112_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; lean_object* v___x_129_; 
v___f_125_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_126_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_127_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_128_ = 0;
v___x_129_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_126_, v___x_127_, v___x_128_, v___f_125_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2____boxed(lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_();
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0(lean_object* v_init_132_, lean_object* v_t_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0(v_init_132_, v_t_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_135_, lean_object* v_t_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0(v_init_135_, v_t_136_);
lean_dec(v_t_136_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(lean_object* v_env_143_, lean_object* v_opts_144_, lean_object* v_procName_145_){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1));
v___x_147_ = l_Lean_Environment_evalConstCheck___redArg(v_env_143_, v_opts_144_, v___x_146_, v_procName_145_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___boxed(lean_object* v_env_148_, lean_object* v_opts_149_, lean_object* v_procName_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(v_env_148_, v_opts_149_, v_procName_150_);
lean_dec_ref(v_opts_149_);
return v_res_151_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_152_, lean_object* v_i_153_, lean_object* v_k_154_){
_start:
{
lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_155_ = lean_array_get_size(v_keys_152_);
v___x_156_ = lean_nat_dec_lt(v_i_153_, v___x_155_);
if (v___x_156_ == 0)
{
lean_dec(v_i_153_);
return v___x_156_;
}
else
{
lean_object* v_k_x27_157_; uint8_t v___x_158_; 
v_k_x27_157_ = lean_array_fget_borrowed(v_keys_152_, v_i_153_);
v___x_158_ = lean_name_eq(v_k_154_, v_k_x27_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_unsigned_to_nat(1u);
v___x_160_ = lean_nat_add(v_i_153_, v___x_159_);
lean_dec(v_i_153_);
v_i_153_ = v___x_160_;
goto _start;
}
else
{
lean_dec(v_i_153_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_162_, lean_object* v_i_163_, lean_object* v_k_164_){
_start:
{
uint8_t v_res_165_; lean_object* v_r_166_; 
v_res_165_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg(v_keys_162_, v_i_163_, v_k_164_);
lean_dec(v_k_164_);
lean_dec_ref(v_keys_162_);
v_r_166_ = lean_box(v_res_165_);
return v_r_166_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg(lean_object* v_x_167_, size_t v_x_168_, lean_object* v_x_169_){
_start:
{
if (lean_obj_tag(v_x_167_) == 0)
{
lean_object* v_es_170_; lean_object* v___x_171_; size_t v___x_172_; size_t v___x_173_; lean_object* v_j_174_; lean_object* v___x_175_; 
v_es_170_ = lean_ctor_get(v_x_167_, 0);
v___x_171_ = lean_box(2);
v___x_172_ = ((size_t)31ULL);
v___x_173_ = lean_usize_land(v_x_168_, v___x_172_);
v_j_174_ = lean_usize_to_nat(v___x_173_);
v___x_175_ = lean_array_get_borrowed(v___x_171_, v_es_170_, v_j_174_);
lean_dec(v_j_174_);
switch(lean_obj_tag(v___x_175_))
{
case 0:
{
lean_object* v_key_176_; uint8_t v___x_177_; 
v_key_176_ = lean_ctor_get(v___x_175_, 0);
v___x_177_ = lean_name_eq(v_x_169_, v_key_176_);
return v___x_177_;
}
case 1:
{
lean_object* v_node_178_; size_t v___x_179_; size_t v___x_180_; 
v_node_178_ = lean_ctor_get(v___x_175_, 0);
v___x_179_ = ((size_t)5ULL);
v___x_180_ = lean_usize_shift_right(v_x_168_, v___x_179_);
v_x_167_ = v_node_178_;
v_x_168_ = v___x_180_;
goto _start;
}
default: 
{
uint8_t v___x_182_; 
v___x_182_ = 0;
return v___x_182_;
}
}
}
else
{
lean_object* v_ks_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v_ks_183_ = lean_ctor_get(v_x_167_, 0);
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg(v_ks_183_, v___x_184_, v_x_169_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___boxed(lean_object* v_x_186_, lean_object* v_x_187_, lean_object* v_x_188_){
_start:
{
size_t v_x_236__boxed_189_; uint8_t v_res_190_; lean_object* v_r_191_; 
v_x_236__boxed_189_ = lean_unbox_usize(v_x_187_);
lean_dec(v_x_187_);
v_res_190_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg(v_x_186_, v_x_236__boxed_189_, v_x_188_);
lean_dec(v_x_188_);
lean_dec_ref(v_x_186_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(lean_object* v_x_192_, lean_object* v_x_193_){
_start:
{
uint64_t v___y_195_; 
if (lean_obj_tag(v_x_193_) == 0)
{
uint64_t v___x_198_; 
v___x_198_ = 1723ULL;
v___y_195_ = v___x_198_;
goto v___jp_194_;
}
else
{
uint64_t v_hash_199_; 
v_hash_199_ = lean_ctor_get_uint64(v_x_193_, sizeof(void*)*2);
v___y_195_ = v_hash_199_;
goto v___jp_194_;
}
v___jp_194_:
{
size_t v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_uint64_to_usize(v___y_195_);
v___x_197_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg(v_x_192_, v___x_196_, v_x_193_);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___boxed(lean_object* v_x_200_, lean_object* v_x_201_){
_start:
{
uint8_t v_res_202_; lean_object* v_r_203_; 
v_res_202_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(v_x_200_, v_x_201_);
lean_dec(v_x_201_);
lean_dec_ref(v_x_200_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_existsBuiltinRpcProcedure(lean_object* v_method_204_){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_206_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_207_ = lean_st_ref_get(v___x_206_);
v___x_208_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(v___x_207_, v_method_204_);
lean_dec(v___x_207_);
v___x_209_ = lean_box(v___x_208_);
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_existsBuiltinRpcProcedure___boxed(lean_object* v_method_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_Server_existsBuiltinRpcProcedure(v_method_211_);
lean_dec(v_method_211_);
return v_res_213_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0(lean_object* v_00_u03b2_214_, lean_object* v_x_215_, lean_object* v_x_216_){
_start:
{
uint8_t v___x_217_; 
v___x_217_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(v_x_215_, v_x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___boxed(lean_object* v_00_u03b2_218_, lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
uint8_t v_res_221_; lean_object* v_r_222_; 
v_res_221_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0(v_00_u03b2_218_, v_x_219_, v_x_220_);
lean_dec(v_x_220_);
lean_dec_ref(v_x_219_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0(lean_object* v_00_u03b2_223_, lean_object* v_x_224_, size_t v_x_225_, lean_object* v_x_226_){
_start:
{
uint8_t v___x_227_; 
v___x_227_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg(v_x_224_, v_x_225_, v_x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___boxed(lean_object* v_00_u03b2_228_, lean_object* v_x_229_, lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
size_t v_x_314__boxed_232_; uint8_t v_res_233_; lean_object* v_r_234_; 
v_x_314__boxed_232_ = lean_unbox_usize(v_x_230_);
lean_dec(v_x_230_);
v_res_233_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0(v_00_u03b2_228_, v_x_229_, v_x_314__boxed_232_, v_x_231_);
lean_dec(v_x_231_);
lean_dec_ref(v_x_229_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_235_, lean_object* v_keys_236_, lean_object* v_vals_237_, lean_object* v_heq_238_, lean_object* v_i_239_, lean_object* v_k_240_){
_start:
{
uint8_t v___x_241_; 
v___x_241_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg(v_keys_236_, v_i_239_, v_k_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_242_, lean_object* v_keys_243_, lean_object* v_vals_244_, lean_object* v_heq_245_, lean_object* v_i_246_, lean_object* v_k_247_){
_start:
{
uint8_t v_res_248_; lean_object* v_r_249_; 
v_res_248_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1(v_00_u03b2_242_, v_keys_243_, v_vals_244_, v_heq_245_, v_i_246_, v_k_247_);
lean_dec(v_k_247_);
lean_dec_ref(v_vals_244_);
lean_dec_ref(v_keys_243_);
v_r_249_ = lean_box(v_res_248_);
return v_r_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1(lean_object* v___y_250_){
_start:
{
lean_object* v_doc_252_; lean_object* v___x_253_; 
v_doc_252_ = lean_ctor_get(v___y_250_, 1);
lean_inc_ref(v_doc_252_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v_doc_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1___boxed(lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1(v___y_254_);
lean_dec_ref(v___y_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__0(lean_object* v_val_257_, uint64_t v_sessionId_258_, lean_object* v_params_259_, lean_object* v___y_260_){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_box_uint64(v_sessionId_258_);
lean_inc_ref(v___y_260_);
v___x_263_ = lean_apply_4(v_val_257_, v___x_262_, v_params_259_, v___y_260_, lean_box(0));
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_277_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_277_ == 0)
{
v___x_266_ = v___x_263_;
v_isShared_267_ = v_isSharedCheck_277_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_263_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_277_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; 
v___x_268_ = lean_io_wait(v_a_264_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_271_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_a_269_);
lean_dec_ref_known(v___x_268_, 1);
if (v_isShared_267_ == 0)
{
lean_ctor_set_tag(v___x_266_, 1);
lean_ctor_set(v___x_266_, 0, v_a_269_);
v___x_271_ = v___x_266_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; 
v_a_273_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_a_273_);
lean_dec_ref_known(v___x_268_, 1);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v_a_273_);
v___x_275_ = v___x_266_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
v_a_278_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_263_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_263_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__0___boxed(lean_object* v_val_286_, lean_object* v_sessionId_287_, lean_object* v_params_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
uint64_t v_sessionId_boxed_291_; lean_object* v_res_292_; 
v_sessionId_boxed_291_ = lean_unbox_uint64(v_sessionId_287_);
lean_dec_ref(v_sessionId_287_);
v_res_292_ = l_Lean_Server_handleRpcCall___lam__0(v_val_286_, v_sessionId_boxed_291_, v_params_288_, v___y_289_);
lean_dec_ref(v___y_289_);
return v_res_292_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_handleRpcCall___lam__1(lean_object* v___x_293_, lean_object* v_method_294_, lean_object* v_s_295_){
_start:
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_295_);
v___x_297_ = lean_nat_dec_le(v___x_293_, v___x_296_);
lean_dec(v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v_toEnvExtension_299_; lean_object* v_asyncMode_300_; lean_object* v___x_301_; uint8_t v___x_302_; lean_object* v___x_303_; 
v___x_298_ = l_Lean_Server_userRpcProcedures;
v_toEnvExtension_299_ = lean_ctor_get(v___x_298_, 0);
v_asyncMode_300_ = lean_ctor_get(v_toEnvExtension_299_, 2);
v___x_301_ = l_Lean_Server_Snapshots_Snapshot_env(v_s_295_);
v___x_302_ = 0;
v___x_303_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_298_, v___x_301_, v_method_294_, v_asyncMode_300_, v___x_302_);
if (lean_obj_tag(v___x_303_) == 0)
{
return v___x_297_;
}
else
{
uint8_t v___x_304_; 
lean_dec_ref_known(v___x_303_, 1);
v___x_304_ = 1;
return v___x_304_;
}
}
else
{
lean_dec(v_method_294_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__1___boxed(lean_object* v___x_305_, lean_object* v_method_306_, lean_object* v_s_307_){
_start:
{
uint8_t v_res_308_; lean_object* v_r_309_; 
v_res_308_ = l_Lean_Server_handleRpcCall___lam__1(v___x_305_, v_method_306_, v_s_307_);
lean_dec_ref(v_s_307_);
lean_dec(v___x_305_);
v_r_309_ = lean_box(v_res_308_);
return v_r_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__2(lean_object* v___x_310_, lean_object* v___y_311_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_310_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__2___boxed(lean_object* v___x_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Server_handleRpcCall___lam__2(v___x_314_, v___y_315_);
lean_dec_ref(v___y_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__3(lean_object* v_method_320_, lean_object* v___x_321_, uint8_t v___x_322_, uint64_t v_sessionId_323_, lean_object* v_params_324_, lean_object* v___x_325_, lean_object* v_snap_326_, lean_object* v___y_327_){
_start:
{
lean_object* v___x_329_; lean_object* v_toEnvExtension_330_; lean_object* v_asyncMode_331_; lean_object* v___x_332_; uint8_t v___x_333_; lean_object* v___x_334_; 
v___x_329_ = l_Lean_Server_userRpcProcedures;
v_toEnvExtension_330_ = lean_ctor_get(v___x_329_, 0);
v_asyncMode_331_ = lean_ctor_get(v_toEnvExtension_330_, 2);
v___x_332_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_326_);
v___x_333_ = 0;
lean_inc_ref(v___x_332_);
v___x_334_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_329_, v___x_332_, v_method_320_, v_asyncMode_331_, v___x_333_);
if (lean_obj_tag(v___x_334_) == 1)
{
lean_object* v_cmdState_335_; lean_object* v_val_336_; lean_object* v_scopes_337_; lean_object* v___x_338_; lean_object* v_opts_339_; lean_object* v___x_340_; 
lean_dec_ref(v___x_325_);
v_cmdState_335_ = lean_ctor_get(v_snap_326_, 2);
v_val_336_ = lean_ctor_get(v___x_334_, 0);
lean_inc_n(v_val_336_, 2);
lean_dec_ref_known(v___x_334_, 1);
v_scopes_337_ = lean_ctor_get(v_cmdState_335_, 2);
v___x_338_ = l_List_head_x21___redArg(v___x_321_, v_scopes_337_);
v_opts_339_ = lean_ctor_get(v___x_338_, 1);
lean_inc_ref(v_opts_339_);
lean_dec(v___x_338_);
v___x_340_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(v___x_332_, v_opts_339_, v_val_336_);
lean_dec_ref(v_opts_339_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_356_; 
lean_dec(v_params_324_);
v_a_341_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_356_ == 0)
{
v___x_343_ = v___x_340_;
v_isShared_344_ = v_isSharedCheck_356_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_340_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_356_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
uint8_t v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_345_ = 4;
v___x_346_ = ((lean_object*)(l_Lean_Server_handleRpcCall___lam__3___closed__0));
v___x_347_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_336_, v___x_322_);
v___x_348_ = lean_string_append(v___x_346_, v___x_347_);
lean_dec_ref(v___x_347_);
v___x_349_ = ((lean_object*)(l_Lean_Server_handleRpcCall___lam__3___closed__1));
v___x_350_ = lean_string_append(v___x_348_, v___x_349_);
v___x_351_ = lean_string_append(v___x_350_, v_a_341_);
lean_dec(v_a_341_);
v___x_352_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_352_, 0, v___x_351_);
lean_ctor_set_uint8(v___x_352_, sizeof(void*)*1, v___x_345_);
if (v_isShared_344_ == 0)
{
lean_ctor_set_tag(v___x_343_, 1);
lean_ctor_set(v___x_343_, 0, v___x_352_);
v___x_354_ = v___x_343_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
else
{
lean_object* v_a_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
lean_dec(v_val_336_);
v_a_357_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_a_357_);
lean_dec_ref_known(v___x_340_, 1);
v___x_358_ = lean_box_uint64(v_sessionId_323_);
lean_inc_ref(v___y_327_);
v___x_359_ = lean_apply_4(v_a_357_, v___x_358_, v_params_324_, v___y_327_, lean_box(0));
return v___x_359_;
}
}
else
{
lean_object* v___x_360_; 
lean_dec(v___x_334_);
lean_dec_ref(v___x_332_);
lean_dec(v_params_324_);
v___x_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_325_);
return v___x_360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__3___boxed(lean_object* v_method_361_, lean_object* v___x_362_, lean_object* v___x_363_, lean_object* v_sessionId_364_, lean_object* v_params_365_, lean_object* v___x_366_, lean_object* v_snap_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
uint8_t v___x_2316__boxed_370_; uint64_t v_sessionId_boxed_371_; lean_object* v_res_372_; 
v___x_2316__boxed_370_ = lean_unbox(v___x_363_);
v_sessionId_boxed_371_ = lean_unbox_uint64(v_sessionId_364_);
lean_dec_ref(v_sessionId_364_);
v_res_372_ = l_Lean_Server_handleRpcCall___lam__3(v_method_361_, v___x_362_, v___x_2316__boxed_370_, v_sessionId_boxed_371_, v_params_365_, v___x_366_, v_snap_367_, v___y_368_);
lean_dec_ref(v___y_368_);
lean_dec_ref(v_snap_367_);
lean_dec_ref(v___x_362_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_373_, lean_object* v_vals_374_, lean_object* v_i_375_, lean_object* v_k_376_){
_start:
{
lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_377_ = lean_array_get_size(v_keys_373_);
v___x_378_ = lean_nat_dec_lt(v_i_375_, v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
lean_dec(v_i_375_);
v___x_379_ = lean_box(0);
return v___x_379_;
}
else
{
lean_object* v_k_x27_380_; uint8_t v___x_381_; 
v_k_x27_380_ = lean_array_fget_borrowed(v_keys_373_, v_i_375_);
v___x_381_ = lean_name_eq(v_k_376_, v_k_x27_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_unsigned_to_nat(1u);
v___x_383_ = lean_nat_add(v_i_375_, v___x_382_);
lean_dec(v_i_375_);
v_i_375_ = v___x_383_;
goto _start;
}
else
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_array_fget_borrowed(v_vals_374_, v_i_375_);
lean_dec(v_i_375_);
lean_inc(v___x_385_);
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_387_, lean_object* v_vals_388_, lean_object* v_i_389_, lean_object* v_k_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(v_keys_387_, v_vals_388_, v_i_389_, v_k_390_);
lean_dec(v_k_390_);
lean_dec_ref(v_vals_388_);
lean_dec_ref(v_keys_387_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(lean_object* v_x_392_, size_t v_x_393_, lean_object* v_x_394_){
_start:
{
if (lean_obj_tag(v_x_392_) == 0)
{
lean_object* v_es_395_; lean_object* v___x_396_; size_t v___x_397_; size_t v___x_398_; lean_object* v_j_399_; lean_object* v___x_400_; 
v_es_395_ = lean_ctor_get(v_x_392_, 0);
v___x_396_ = lean_box(2);
v___x_397_ = ((size_t)31ULL);
v___x_398_ = lean_usize_land(v_x_393_, v___x_397_);
v_j_399_ = lean_usize_to_nat(v___x_398_);
v___x_400_ = lean_array_get_borrowed(v___x_396_, v_es_395_, v_j_399_);
lean_dec(v_j_399_);
switch(lean_obj_tag(v___x_400_))
{
case 0:
{
lean_object* v_key_401_; lean_object* v_val_402_; uint8_t v___x_403_; 
v_key_401_ = lean_ctor_get(v___x_400_, 0);
v_val_402_ = lean_ctor_get(v___x_400_, 1);
v___x_403_ = lean_name_eq(v_x_394_, v_key_401_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; 
v___x_404_ = lean_box(0);
return v___x_404_;
}
else
{
lean_object* v___x_405_; 
lean_inc(v_val_402_);
v___x_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_405_, 0, v_val_402_);
return v___x_405_;
}
}
case 1:
{
lean_object* v_node_406_; size_t v___x_407_; size_t v___x_408_; 
v_node_406_ = lean_ctor_get(v___x_400_, 0);
v___x_407_ = ((size_t)5ULL);
v___x_408_ = lean_usize_shift_right(v_x_393_, v___x_407_);
v_x_392_ = v_node_406_;
v_x_393_ = v___x_408_;
goto _start;
}
default: 
{
lean_object* v___x_410_; 
v___x_410_ = lean_box(0);
return v___x_410_;
}
}
}
else
{
lean_object* v_ks_411_; lean_object* v_vs_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_ks_411_ = lean_ctor_get(v_x_392_, 0);
v_vs_412_ = lean_ctor_get(v_x_392_, 1);
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(v_ks_411_, v_vs_412_, v___x_413_, v_x_394_);
return v___x_414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg___boxed(lean_object* v_x_415_, lean_object* v_x_416_, lean_object* v_x_417_){
_start:
{
size_t v_x_2405__boxed_418_; lean_object* v_res_419_; 
v_x_2405__boxed_418_ = lean_unbox_usize(v_x_416_);
lean_dec(v_x_416_);
v_res_419_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(v_x_415_, v_x_2405__boxed_418_, v_x_417_);
lean_dec(v_x_417_);
lean_dec_ref(v_x_415_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
uint64_t v___y_423_; 
if (lean_obj_tag(v_x_421_) == 0)
{
uint64_t v___x_426_; 
v___x_426_ = 1723ULL;
v___y_423_ = v___x_426_;
goto v___jp_422_;
}
else
{
uint64_t v_hash_427_; 
v_hash_427_ = lean_ctor_get_uint64(v_x_421_, sizeof(void*)*2);
v___y_423_ = v_hash_427_;
goto v___jp_422_;
}
v___jp_422_:
{
size_t v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_uint64_to_usize(v___y_423_);
v___x_425_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(v_x_420_, v___x_424_, v_x_421_);
return v___x_425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg___boxed(lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(v_x_428_, v_x_429_);
lean_dec(v_x_429_);
lean_dec_ref(v_x_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall(lean_object* v_p_433_, lean_object* v_a_434_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v_toTextDocumentPositionParams_439_; uint64_t v_sessionId_440_; lean_object* v_method_441_; lean_object* v_params_442_; lean_object* v___x_443_; 
v___x_436_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_437_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_438_ = lean_st_ref_get(v___x_437_);
v_toTextDocumentPositionParams_439_ = lean_ctor_get(v_p_433_, 0);
lean_inc_ref(v_toTextDocumentPositionParams_439_);
v_sessionId_440_ = lean_ctor_get_uint64(v_p_433_, sizeof(void*)*3);
v_method_441_ = lean_ctor_get(v_p_433_, 1);
lean_inc(v_method_441_);
v_params_442_ = lean_ctor_get(v_p_433_, 2);
lean_inc(v_params_442_);
lean_dec_ref(v_p_433_);
v___x_443_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(v___x_438_, v_method_441_);
lean_dec(v___x_438_);
if (lean_obj_tag(v___x_443_) == 1)
{
lean_object* v_val_444_; lean_object* v___x_445_; lean_object* v___f_446_; lean_object* v___x_447_; 
lean_dec(v_method_441_);
lean_dec_ref(v_toTextDocumentPositionParams_439_);
v_val_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_val_444_);
lean_dec_ref_known(v___x_443_, 1);
v___x_445_ = lean_box_uint64(v_sessionId_440_);
v___f_446_ = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__0___boxed), 5, 3);
lean_closure_set(v___f_446_, 0, v_val_444_);
lean_closure_set(v___f_446_, 1, v___x_445_);
lean_closure_set(v___f_446_, 2, v_params_442_);
v___x_447_ = l_Lean_Server_RequestM_asTask___redArg(v___f_446_, v_a_434_);
return v___x_447_;
}
else
{
lean_object* v___x_448_; lean_object* v_a_449_; lean_object* v_toEditableDocumentCore_450_; lean_object* v_meta_451_; lean_object* v_text_452_; lean_object* v_position_453_; lean_object* v___x_454_; lean_object* v___f_455_; uint8_t v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___f_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___f_467_; lean_object* v___x_468_; 
lean_dec(v___x_443_);
v___x_448_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1(v_a_434_);
v_a_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_a_449_);
lean_dec_ref(v___x_448_);
v_toEditableDocumentCore_450_ = lean_ctor_get(v_a_449_, 0);
v_meta_451_ = lean_ctor_get(v_toEditableDocumentCore_450_, 0);
v_text_452_ = lean_ctor_get(v_meta_451_, 3);
v_position_453_ = lean_ctor_get(v_toTextDocumentPositionParams_439_, 1);
lean_inc_ref(v_position_453_);
lean_dec_ref(v_toTextDocumentPositionParams_439_);
v___x_454_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_452_, v_position_453_);
lean_inc_n(v_method_441_, 2);
v___f_455_ = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__1___boxed), 3, 2);
lean_closure_set(v___f_455_, 0, v___x_454_);
lean_closure_set(v___f_455_, 1, v_method_441_);
v___x_456_ = 2;
v___x_457_ = ((lean_object*)(l_Lean_Server_handleRpcCall___closed__0));
v___x_458_ = 1;
v___x_459_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_441_, v___x_458_);
v___x_460_ = lean_string_append(v___x_457_, v___x_459_);
lean_dec_ref(v___x_459_);
v___x_461_ = ((lean_object*)(l_Lean_Server_handleRpcCall___closed__1));
v___x_462_ = lean_string_append(v___x_460_, v___x_461_);
v___x_463_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set_uint8(v___x_463_, sizeof(void*)*1, v___x_456_);
lean_inc_ref(v___x_463_);
v___f_464_ = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__2___boxed), 3, 1);
lean_closure_set(v___f_464_, 0, v___x_463_);
v___x_465_ = lean_box(v___x_458_);
v___x_466_ = lean_box_uint64(v_sessionId_440_);
v___f_467_ = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__3___boxed), 9, 6);
lean_closure_set(v___f_467_, 0, v_method_441_);
lean_closure_set(v___f_467_, 1, v___x_436_);
lean_closure_set(v___f_467_, 2, v___x_465_);
lean_closure_set(v___f_467_, 3, v___x_466_);
lean_closure_set(v___f_467_, 4, v_params_442_);
lean_closure_set(v___f_467_, 5, v___x_463_);
v___x_468_ = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(v_a_449_, v___f_455_, v___f_464_, v___f_467_, v_a_434_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___boxed(lean_object* v_p_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Server_handleRpcCall(v_p_469_, v_a_470_);
lean_dec_ref(v_a_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0(lean_object* v_00_u03b2_473_, lean_object* v_x_474_, lean_object* v_x_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(v_x_474_, v_x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___boxed(lean_object* v_00_u03b2_477_, lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0(v_00_u03b2_477_, v_x_478_, v_x_479_);
lean_dec(v_x_479_);
lean_dec_ref(v_x_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0(lean_object* v_00_u03b2_481_, lean_object* v_x_482_, size_t v_x_483_, lean_object* v_x_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(v_x_482_, v_x_483_, v_x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___boxed(lean_object* v_00_u03b2_486_, lean_object* v_x_487_, lean_object* v_x_488_, lean_object* v_x_489_){
_start:
{
size_t v_x_2536__boxed_490_; lean_object* v_res_491_; 
v_x_2536__boxed_490_ = lean_unbox_usize(v_x_488_);
lean_dec(v_x_488_);
v_res_491_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0(v_00_u03b2_486_, v_x_487_, v_x_2536__boxed_490_, v_x_489_);
lean_dec(v_x_489_);
lean_dec_ref(v_x_487_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_492_, lean_object* v_keys_493_, lean_object* v_vals_494_, lean_object* v_heq_495_, lean_object* v_i_496_, lean_object* v_k_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(v_keys_493_, v_vals_494_, v_i_496_, v_k_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_499_, lean_object* v_keys_500_, lean_object* v_vals_501_, lean_object* v_heq_502_, lean_object* v_i_503_, lean_object* v_k_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2(v_00_u03b2_499_, v_keys_500_, v_vals_501_, v_heq_502_, v_i_503_, v_k_504_);
lean_dec(v_k_504_);
lean_dec_ref(v_vals_501_);
lean_dec_ref(v_keys_500_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_506_, uint8_t v_val_507_, lean_object* v___y_508_){
_start:
{
if (lean_obj_tag(v___y_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec(v_serialize_x3f_506_);
v_a_509_ = lean_ctor_get(v___y_508_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___y_508_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___y_508_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___y_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
else
{
if (lean_obj_tag(v_serialize_x3f_506_) == 1)
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_528_; 
v_a_517_ = lean_ctor_get(v___y_508_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___y_508_);
if (v_isSharedCheck_528_ == 0)
{
v___x_519_ = v___y_508_;
v_isShared_520_ = v_isSharedCheck_528_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___y_508_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_528_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v_val_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v_val_521_ = lean_ctor_get(v_serialize_x3f_506_, 0);
lean_inc(v_val_521_);
lean_dec_ref_known(v_serialize_x3f_506_, 1);
v___x_522_ = lean_box(0);
v___x_523_ = lean_apply_1(v_val_521_, v_a_517_);
v___x_524_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*2, v_val_507_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v___x_524_);
v___x_526_ = v___x_519_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_539_; 
lean_dec(v_serialize_x3f_506_);
v_a_529_ = lean_ctor_get(v___y_508_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___y_508_);
if (v_isSharedCheck_539_ == 0)
{
v___x_531_ = v___y_508_;
v_isShared_532_ = v_isSharedCheck_539_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___y_508_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_539_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
lean_inc(v_a_529_);
v___x_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_533_, 0, v_a_529_);
v___x_534_ = l_Lean_Json_compress(v_a_529_);
v___x_535_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*2, v_val_507_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_535_);
v___x_537_ = v___x_531_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_540_, lean_object* v_val_541_, lean_object* v___y_542_){
_start:
{
uint8_t v_val_789__boxed_543_; lean_object* v_res_544_; 
v_val_789__boxed_543_ = lean_unbox(v_val_541_);
v_res_544_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_540_, v_val_789__boxed_543_, v___y_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8___redArg(lean_object* v_x_545_, lean_object* v_x_546_, lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
lean_object* v_ks_549_; lean_object* v_vs_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_574_; 
v_ks_549_ = lean_ctor_get(v_x_545_, 0);
v_vs_550_ = lean_ctor_get(v_x_545_, 1);
v_isSharedCheck_574_ = !lean_is_exclusive(v_x_545_);
if (v_isSharedCheck_574_ == 0)
{
v___x_552_ = v_x_545_;
v_isShared_553_ = v_isSharedCheck_574_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_vs_550_);
lean_inc(v_ks_549_);
lean_dec(v_x_545_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_574_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = lean_array_get_size(v_ks_549_);
v___x_555_ = lean_nat_dec_lt(v_x_546_, v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
lean_dec(v_x_546_);
v___x_556_ = lean_array_push(v_ks_549_, v_x_547_);
v___x_557_ = lean_array_push(v_vs_550_, v_x_548_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v___x_557_);
lean_ctor_set(v___x_552_, 0, v___x_556_);
v___x_559_ = v___x_552_;
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
else
{
lean_object* v_k_x27_561_; uint8_t v___x_562_; 
v_k_x27_561_ = lean_array_fget_borrowed(v_ks_549_, v_x_546_);
v___x_562_ = lean_string_dec_eq(v_x_547_, v_k_x27_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_564_; 
if (v_isShared_553_ == 0)
{
v___x_564_ = v___x_552_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_ks_549_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_vs_550_);
v___x_564_ = v_reuseFailAlloc_568_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_unsigned_to_nat(1u);
v___x_566_ = lean_nat_add(v_x_546_, v___x_565_);
lean_dec(v_x_546_);
v_x_545_ = v___x_564_;
v_x_546_ = v___x_566_;
goto _start;
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_569_ = lean_array_fset(v_ks_549_, v_x_546_, v_x_547_);
v___x_570_ = lean_array_fset(v_vs_550_, v_x_546_, v_x_548_);
lean_dec(v_x_546_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v___x_570_);
lean_ctor_set(v___x_552_, 0, v___x_569_);
v___x_572_ = v___x_552_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7___redArg(lean_object* v_n_575_, lean_object* v_k_576_, lean_object* v_v_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_unsigned_to_nat(0u);
v___x_579_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8___redArg(v_n_575_, v___x_578_, v_k_576_, v_v_577_);
return v___x_579_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* v_x_581_, size_t v_x_582_, size_t v_x_583_, lean_object* v_x_584_, lean_object* v_x_585_){
_start:
{
if (lean_obj_tag(v_x_581_) == 0)
{
lean_object* v_es_586_; size_t v___x_587_; size_t v___x_588_; lean_object* v_j_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v_es_586_ = lean_ctor_get(v_x_581_, 0);
v___x_587_ = ((size_t)31ULL);
v___x_588_ = lean_usize_land(v_x_582_, v___x_587_);
v_j_589_ = lean_usize_to_nat(v___x_588_);
v___x_590_ = lean_array_get_size(v_es_586_);
v___x_591_ = lean_nat_dec_lt(v_j_589_, v___x_590_);
if (v___x_591_ == 0)
{
lean_dec(v_j_589_);
lean_dec(v_x_585_);
lean_dec_ref(v_x_584_);
return v_x_581_;
}
else
{
lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_630_; 
lean_inc_ref(v_es_586_);
v_isSharedCheck_630_ = !lean_is_exclusive(v_x_581_);
if (v_isSharedCheck_630_ == 0)
{
lean_object* v_unused_631_; 
v_unused_631_ = lean_ctor_get(v_x_581_, 0);
lean_dec(v_unused_631_);
v___x_593_ = v_x_581_;
v_isShared_594_ = v_isSharedCheck_630_;
goto v_resetjp_592_;
}
else
{
lean_dec(v_x_581_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_630_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v_v_595_; lean_object* v___x_596_; lean_object* v_xs_x27_597_; lean_object* v___y_599_; 
v_v_595_ = lean_array_fget(v_es_586_, v_j_589_);
v___x_596_ = lean_box(0);
v_xs_x27_597_ = lean_array_fset(v_es_586_, v_j_589_, v___x_596_);
switch(lean_obj_tag(v_v_595_))
{
case 0:
{
lean_object* v_key_604_; lean_object* v_val_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_615_; 
v_key_604_ = lean_ctor_get(v_v_595_, 0);
v_val_605_ = lean_ctor_get(v_v_595_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v_v_595_);
if (v_isSharedCheck_615_ == 0)
{
v___x_607_ = v_v_595_;
v_isShared_608_ = v_isSharedCheck_615_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_val_605_);
lean_inc(v_key_604_);
lean_dec(v_v_595_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_615_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
uint8_t v___x_609_; 
v___x_609_ = lean_string_dec_eq(v_x_584_, v_key_604_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
lean_del_object(v___x_607_);
v___x_610_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_604_, v_val_605_, v_x_584_, v_x_585_);
v___x_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
v___y_599_ = v___x_611_;
goto v___jp_598_;
}
else
{
lean_object* v___x_613_; 
lean_dec(v_val_605_);
lean_dec(v_key_604_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v_x_585_);
lean_ctor_set(v___x_607_, 0, v_x_584_);
v___x_613_ = v___x_607_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_x_584_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_x_585_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
v___y_599_ = v___x_613_;
goto v___jp_598_;
}
}
}
}
case 1:
{
lean_object* v_node_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_628_; 
v_node_616_ = lean_ctor_get(v_v_595_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v_v_595_);
if (v_isSharedCheck_628_ == 0)
{
v___x_618_ = v_v_595_;
v_isShared_619_ = v_isSharedCheck_628_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_node_616_);
lean_dec(v_v_595_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_628_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
size_t v___x_620_; size_t v___x_621_; size_t v___x_622_; size_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_620_ = ((size_t)5ULL);
v___x_621_ = lean_usize_shift_right(v_x_582_, v___x_620_);
v___x_622_ = ((size_t)1ULL);
v___x_623_ = lean_usize_add(v_x_583_, v___x_622_);
v___x_624_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_node_616_, v___x_621_, v___x_623_, v_x_584_, v_x_585_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_624_);
v___x_626_ = v___x_618_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
v___y_599_ = v___x_626_;
goto v___jp_598_;
}
}
}
default: 
{
lean_object* v___x_629_; 
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v_x_584_);
lean_ctor_set(v___x_629_, 1, v_x_585_);
v___y_599_ = v___x_629_;
goto v___jp_598_;
}
}
v___jp_598_:
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = lean_array_fset(v_xs_x27_597_, v_j_589_, v___y_599_);
lean_dec(v_j_589_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_600_);
v___x_602_ = v___x_593_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
else
{
lean_object* v_ks_632_; lean_object* v_vs_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_651_; 
v_ks_632_ = lean_ctor_get(v_x_581_, 0);
v_vs_633_ = lean_ctor_get(v_x_581_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_x_581_);
if (v_isSharedCheck_651_ == 0)
{
v___x_635_ = v_x_581_;
v_isShared_636_ = v_isSharedCheck_651_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_vs_633_);
lean_inc(v_ks_632_);
lean_dec(v_x_581_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_651_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_ks_632_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_vs_633_);
v___x_638_ = v_reuseFailAlloc_650_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v_newNode_639_; size_t v___x_640_; uint8_t v___x_641_; 
v_newNode_639_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7___redArg(v___x_638_, v_x_584_, v_x_585_);
v___x_640_ = ((size_t)7ULL);
v___x_641_ = lean_usize_dec_le(v___x_640_, v_x_583_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_642_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_639_);
v___x_643_ = lean_unsigned_to_nat(4u);
v___x_644_ = lean_nat_dec_lt(v___x_642_, v___x_643_);
lean_dec(v___x_642_);
if (v___x_644_ == 0)
{
lean_object* v_ks_645_; lean_object* v_vs_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v_ks_645_ = lean_ctor_get(v_newNode_639_, 0);
lean_inc_ref(v_ks_645_);
v_vs_646_ = lean_ctor_get(v_newNode_639_, 1);
lean_inc_ref(v_vs_646_);
lean_dec_ref(v_newNode_639_);
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
v___x_649_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_x_583_, v_ks_645_, v_vs_646_, v___x_647_, v___x_648_);
lean_dec_ref(v_vs_646_);
lean_dec_ref(v_ks_645_);
return v___x_649_;
}
else
{
return v_newNode_639_;
}
}
else
{
return v_newNode_639_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(size_t v_depth_652_, lean_object* v_keys_653_, lean_object* v_vals_654_, lean_object* v_i_655_, lean_object* v_entries_656_){
_start:
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = lean_array_get_size(v_keys_653_);
v___x_658_ = lean_nat_dec_lt(v_i_655_, v___x_657_);
if (v___x_658_ == 0)
{
lean_dec(v_i_655_);
return v_entries_656_;
}
else
{
lean_object* v_k_659_; lean_object* v_v_660_; uint64_t v___x_661_; size_t v_h_662_; size_t v___x_663_; lean_object* v___x_664_; size_t v___x_665_; size_t v___x_666_; size_t v___x_667_; size_t v_h_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_k_659_ = lean_array_fget_borrowed(v_keys_653_, v_i_655_);
v_v_660_ = lean_array_fget_borrowed(v_vals_654_, v_i_655_);
v___x_661_ = lean_string_hash(v_k_659_);
v_h_662_ = lean_uint64_to_usize(v___x_661_);
v___x_663_ = ((size_t)5ULL);
v___x_664_ = lean_unsigned_to_nat(1u);
v___x_665_ = ((size_t)1ULL);
v___x_666_ = lean_usize_sub(v_depth_652_, v___x_665_);
v___x_667_ = lean_usize_mul(v___x_663_, v___x_666_);
v_h_668_ = lean_usize_shift_right(v_h_662_, v___x_667_);
v___x_669_ = lean_nat_add(v_i_655_, v___x_664_);
lean_dec(v_i_655_);
lean_inc(v_v_660_);
lean_inc(v_k_659_);
v___x_670_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_entries_656_, v_h_668_, v_depth_652_, v_k_659_, v_v_660_);
v_i_655_ = v___x_669_;
v_entries_656_ = v___x_670_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_depth_672_, lean_object* v_keys_673_, lean_object* v_vals_674_, lean_object* v_i_675_, lean_object* v_entries_676_){
_start:
{
size_t v_depth_boxed_677_; lean_object* v_res_678_; 
v_depth_boxed_677_ = lean_unbox_usize(v_depth_672_);
lean_dec(v_depth_672_);
v_res_678_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_depth_boxed_677_, v_keys_673_, v_vals_674_, v_i_675_, v_entries_676_);
lean_dec_ref(v_vals_674_);
lean_dec_ref(v_keys_673_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_x_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
size_t v_x_934__boxed_684_; size_t v_x_935__boxed_685_; lean_object* v_res_686_; 
v_x_934__boxed_684_ = lean_unbox_usize(v_x_680_);
lean_dec(v_x_680_);
v_x_935__boxed_685_ = lean_unbox_usize(v_x_681_);
lean_dec(v_x_681_);
v_res_686_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_679_, v_x_934__boxed_684_, v_x_935__boxed_685_, v_x_682_, v_x_683_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* v_x_687_, lean_object* v_x_688_, lean_object* v_x_689_){
_start:
{
uint64_t v___x_690_; size_t v___x_691_; size_t v___x_692_; lean_object* v___x_693_; 
v___x_690_ = lean_string_hash(v_x_688_);
v___x_691_ = lean_uint64_to_usize(v___x_690_);
v___x_692_ = ((size_t)1ULL);
v___x_693_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_687_, v___x_691_, v___x_692_, v_x_688_, v_x_689_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_696_){
_start:
{
lean_object* v___x_697_; 
lean_inc(v_params_696_);
v___x_697_ = l_Lean_Lsp_instFromJsonRpcCallParams_fromJson(v_params_696_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_713_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_713_ == 0)
{
v___x_700_ = v___x_697_;
v_isShared_701_ = v_isSharedCheck_713_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_697_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_713_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
uint8_t v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_702_ = 3;
v___x_703_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_704_ = l_Lean_Json_compress(v_params_696_);
v___x_705_ = lean_string_append(v___x_703_, v___x_704_);
lean_dec_ref(v___x_704_);
v___x_706_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__1));
v___x_707_ = lean_string_append(v___x_705_, v___x_706_);
v___x_708_ = lean_string_append(v___x_707_, v_a_698_);
lean_dec(v_a_698_);
v___x_709_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set_uint8(v___x_709_, sizeof(void*)*1, v___x_702_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v___x_709_);
v___x_711_ = v___x_700_;
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
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec(v_params_696_);
v_a_714_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_697_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_697_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
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
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_722_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0(v_params_722_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set_tag(v___x_727_, 1);
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
v_a_733_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_724_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_724_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
lean_ctor_set_tag(v___x_735_, 0);
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_741_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_744_, lean_object* v___f_745_, lean_object* v_j_746_, lean_object* v___y_747_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_746_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_751_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_a_750_);
lean_dec_ref_known(v___x_749_, 1);
lean_inc_ref(v___y_747_);
v___x_751_ = lean_apply_3(v_handler_744_, v_a_750_, v___y_747_, lean_box(0));
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_760_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_760_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_760_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_760_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_756_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_745_, v_a_752_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_756_);
v___x_758_ = v___x_754_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec_ref(v___f_745_);
v_a_761_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_751_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_751_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec_ref(v___f_745_);
lean_dec_ref(v_handler_744_);
v_a_769_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_749_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_749_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_777_, lean_object* v___f_778_, lean_object* v_j_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2(v_handler_777_, v___f_778_, v_j_779_, v___y_780_);
lean_dec_ref(v___y_780_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0(v_j_783_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_802_; 
v_a_793_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_802_ == 0)
{
v___x_795_ = v___x_784_;
v_isShared_796_ = v_isSharedCheck_802_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_784_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_802_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_toTextDocumentPositionParams_797_; lean_object* v_textDocument_798_; lean_object* v___x_800_; 
v_toTextDocumentPositionParams_797_ = lean_ctor_get(v_a_793_, 0);
lean_inc_ref(v_toTextDocumentPositionParams_797_);
lean_dec(v_a_793_);
v_textDocument_798_ = lean_ctor_get(v_toTextDocumentPositionParams_797_, 0);
lean_inc_ref(v_textDocument_798_);
lean_dec_ref(v_toTextDocumentPositionParams_797_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v_textDocument_798_);
v___x_800_ = v___x_795_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_textDocument_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_keys_803_, lean_object* v_i_804_, lean_object* v_k_805_){
_start:
{
lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_806_ = lean_array_get_size(v_keys_803_);
v___x_807_ = lean_nat_dec_lt(v_i_804_, v___x_806_);
if (v___x_807_ == 0)
{
lean_dec(v_i_804_);
return v___x_807_;
}
else
{
lean_object* v_k_x27_808_; uint8_t v___x_809_; 
v_k_x27_808_ = lean_array_fget_borrowed(v_keys_803_, v_i_804_);
v___x_809_ = lean_string_dec_eq(v_k_805_, v_k_x27_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_unsigned_to_nat(1u);
v___x_811_ = lean_nat_add(v_i_804_, v___x_810_);
lean_dec(v_i_804_);
v_i_804_ = v___x_811_;
goto _start;
}
else
{
lean_dec(v_i_804_);
return v___x_807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_keys_813_, lean_object* v_i_814_, lean_object* v_k_815_){
_start:
{
uint8_t v_res_816_; lean_object* v_r_817_; 
v_res_816_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(v_keys_813_, v_i_814_, v_k_815_);
lean_dec_ref(v_k_815_);
lean_dec_ref(v_keys_813_);
v_r_817_ = lean_box(v_res_816_);
return v_r_817_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object* v_x_818_, size_t v_x_819_, lean_object* v_x_820_){
_start:
{
if (lean_obj_tag(v_x_818_) == 0)
{
lean_object* v_es_821_; lean_object* v___x_822_; size_t v___x_823_; size_t v___x_824_; lean_object* v_j_825_; lean_object* v___x_826_; 
v_es_821_ = lean_ctor_get(v_x_818_, 0);
v___x_822_ = lean_box(2);
v___x_823_ = ((size_t)31ULL);
v___x_824_ = lean_usize_land(v_x_819_, v___x_823_);
v_j_825_ = lean_usize_to_nat(v___x_824_);
v___x_826_ = lean_array_get_borrowed(v___x_822_, v_es_821_, v_j_825_);
lean_dec(v_j_825_);
switch(lean_obj_tag(v___x_826_))
{
case 0:
{
lean_object* v_key_827_; uint8_t v___x_828_; 
v_key_827_ = lean_ctor_get(v___x_826_, 0);
v___x_828_ = lean_string_dec_eq(v_x_820_, v_key_827_);
return v___x_828_;
}
case 1:
{
lean_object* v_node_829_; size_t v___x_830_; size_t v___x_831_; 
v_node_829_ = lean_ctor_get(v___x_826_, 0);
v___x_830_ = ((size_t)5ULL);
v___x_831_ = lean_usize_shift_right(v_x_819_, v___x_830_);
v_x_818_ = v_node_829_;
v_x_819_ = v___x_831_;
goto _start;
}
default: 
{
uint8_t v___x_833_; 
v___x_833_ = 0;
return v___x_833_;
}
}
}
else
{
lean_object* v_ks_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v_ks_834_ = lean_ctor_get(v_x_818_, 0);
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(v_ks_834_, v___x_835_, v_x_820_);
return v___x_836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
size_t v_x_1304__boxed_840_; uint8_t v_res_841_; lean_object* v_r_842_; 
v_x_1304__boxed_840_ = lean_unbox_usize(v_x_838_);
lean_dec(v_x_838_);
v_res_841_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_837_, v_x_1304__boxed_840_, v_x_839_);
lean_dec_ref(v_x_839_);
lean_dec_ref(v_x_837_);
v_r_842_ = lean_box(v_res_841_);
return v_r_842_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_843_, lean_object* v_x_844_){
_start:
{
uint64_t v___x_845_; size_t v___x_846_; uint8_t v___x_847_; 
v___x_845_ = lean_string_hash(v_x_844_);
v___x_846_ = lean_uint64_to_usize(v___x_845_);
v___x_847_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_843_, v___x_846_, v_x_844_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
uint8_t v_res_850_; lean_object* v_r_851_; 
v_res_850_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_848_, v_x_849_);
lean_dec_ref(v_x_849_);
lean_dec_ref(v_x_848_);
v_r_851_ = lean_box(v_res_850_);
return v_r_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0(lean_object* v_method_856_, lean_object* v_handler_857_, lean_object* v_serialize_x3f_858_){
_start:
{
lean_object* v___f_860_; uint8_t v___x_861_; 
v___f_860_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__0));
v___x_861_ = l_Lean_initializing();
if (v___x_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec(v_serialize_x3f_858_);
lean_dec_ref(v_handler_857_);
v___x_862_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__1));
v___x_863_ = lean_string_append(v___x_862_, v_method_856_);
lean_dec_ref(v_method_856_);
v___x_864_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__2));
v___x_865_ = lean_string_append(v___x_863_, v___x_864_);
v___x_866_ = lean_mk_io_user_error(v___x_865_);
v___x_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
return v___x_867_;
}
else
{
lean_object* v___x_868_; lean_object* v___f_869_; lean_object* v___f_870_; lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_868_ = lean_box(v___x_861_);
v___f_869_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_869_, 0, v_serialize_x3f_858_);
lean_closure_set(v___f_869_, 1, v___x_868_);
v___f_870_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_870_, 0, v_handler_857_);
lean_closure_set(v___f_870_, 1, v___f_869_);
v___x_871_ = l_Lean_Server_requestHandlers;
v___x_872_ = lean_st_ref_get(v___x_871_);
v___x_873_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_872_, v_method_856_);
lean_dec(v___x_872_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_874_ = lean_st_ref_take(v___x_871_);
v___x_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_875_, 0, v___f_860_);
lean_ctor_set(v___x_875_, 1, v___f_870_);
v___x_876_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_874_, v_method_856_, v___x_875_);
v___x_877_ = lean_st_ref_put(v___x_871_, v___x_876_);
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
return v___x_878_;
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
lean_dec_ref(v___f_870_);
v___x_879_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__1));
v___x_880_ = lean_string_append(v___x_879_, v_method_856_);
lean_dec_ref(v_method_856_);
v___x_881_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__3));
v___x_882_ = lean_string_append(v___x_880_, v___x_881_);
v___x_883_ = lean_mk_io_user_error(v___x_882_);
v___x_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
return v___x_884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_885_, lean_object* v_handler_886_, lean_object* v_serialize_x3f_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0(v_method_885_, v_handler_886_, v_serialize_x3f_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_893_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_));
v___x_894_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_));
v___x_895_ = lean_box(0);
v___x_896_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0(v___x_893_, v___x_894_, v___x_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2____boxed(lean_object* v_a_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_();
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_899_, lean_object* v_a_900_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_899_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1(v_params_903_, v_a_904_);
lean_dec_ref(v_a_904_);
return v_res_906_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_907_, lean_object* v_x_908_, lean_object* v_x_909_){
_start:
{
uint8_t v___x_910_; 
v___x_910_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_908_, v_x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_911_, lean_object* v_x_912_, lean_object* v_x_913_){
_start:
{
uint8_t v_res_914_; lean_object* v_r_915_; 
v_res_914_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_911_, v_x_912_, v_x_913_);
lean_dec_ref(v_x_913_);
lean_dec_ref(v_x_912_);
v_r_915_ = lean_box(v_res_914_);
return v_r_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_00_u03b2_916_, lean_object* v_x_917_, lean_object* v_x_918_, lean_object* v_x_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_917_, v_x_918_, v_x_919_);
return v___x_920_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object* v_00_u03b2_921_, lean_object* v_x_922_, size_t v_x_923_, lean_object* v_x_924_){
_start:
{
uint8_t v___x_925_; 
v___x_925_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_922_, v_x_923_, v_x_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_926_, lean_object* v_x_927_, lean_object* v_x_928_, lean_object* v_x_929_){
_start:
{
size_t v_x_1461__boxed_930_; uint8_t v_res_931_; lean_object* v_r_932_; 
v_x_1461__boxed_930_ = lean_unbox_usize(v_x_928_);
lean_dec(v_x_928_);
v_res_931_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_00_u03b2_926_, v_x_927_, v_x_1461__boxed_930_, v_x_929_);
lean_dec_ref(v_x_929_);
lean_dec_ref(v_x_927_);
v_r_932_ = lean_box(v_res_931_);
return v_r_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* v_00_u03b2_933_, lean_object* v_x_934_, size_t v_x_935_, size_t v_x_936_, lean_object* v_x_937_, lean_object* v_x_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_934_, v_x_935_, v_x_936_, v_x_937_, v_x_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_940_, lean_object* v_x_941_, lean_object* v_x_942_, lean_object* v_x_943_, lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
size_t v_x_1472__boxed_946_; size_t v_x_1473__boxed_947_; lean_object* v_res_948_; 
v_x_1472__boxed_946_ = lean_unbox_usize(v_x_942_);
lean_dec(v_x_942_);
v_x_1473__boxed_947_ = lean_unbox_usize(v_x_943_);
lean_dec(v_x_943_);
v_res_948_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_940_, v_x_941_, v_x_1472__boxed_946_, v_x_1473__boxed_947_, v_x_944_, v_x_945_);
return v_res_948_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_949_, lean_object* v_keys_950_, lean_object* v_vals_951_, lean_object* v_heq_952_, lean_object* v_i_953_, lean_object* v_k_954_){
_start:
{
uint8_t v___x_955_; 
v___x_955_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(v_keys_950_, v_i_953_, v_k_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_956_, lean_object* v_keys_957_, lean_object* v_vals_958_, lean_object* v_heq_959_, lean_object* v_i_960_, lean_object* v_k_961_){
_start:
{
uint8_t v_res_962_; lean_object* v_r_963_; 
v_res_962_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4(v_00_u03b2_956_, v_keys_957_, v_vals_958_, v_heq_959_, v_i_960_, v_k_961_);
lean_dec_ref(v_k_961_);
lean_dec_ref(v_vals_958_);
lean_dec_ref(v_keys_957_);
v_r_963_ = lean_box(v_res_962_);
return v_r_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_964_, lean_object* v_n_965_, lean_object* v_k_966_, lean_object* v_v_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7___redArg(v_n_965_, v_k_966_, v_v_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_969_, size_t v_depth_970_, lean_object* v_keys_971_, lean_object* v_vals_972_, lean_object* v_heq_973_, lean_object* v_i_974_, lean_object* v_entries_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_depth_970_, v_keys_971_, v_vals_972_, v_i_974_, v_entries_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_977_, lean_object* v_depth_978_, lean_object* v_keys_979_, lean_object* v_vals_980_, lean_object* v_heq_981_, lean_object* v_i_982_, lean_object* v_entries_983_){
_start:
{
size_t v_depth_boxed_984_; lean_object* v_res_985_; 
v_depth_boxed_984_ = lean_unbox_usize(v_depth_978_);
lean_dec(v_depth_978_);
v_res_985_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(v_00_u03b2_977_, v_depth_boxed_984_, v_keys_979_, v_vals_980_, v_heq_981_, v_i_982_, v_entries_983_);
lean_dec_ref(v_vals_980_);
lean_dec_ref(v_keys_979_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8(lean_object* v_00_u03b2_986_, lean_object* v_x_987_, lean_object* v_x_988_, lean_object* v_x_989_, lean_object* v_x_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8___redArg(v_x_987_, v_x_988_, v_x_989_, v_x_990_);
return v___x_991_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_wrapRpcProcedure___redArg___lam__0(uint64_t v_x_992_, uint64_t v_y_993_){
_start:
{
uint8_t v___x_994_; 
v___x_994_ = lean_uint64_dec_lt(v_x_992_, v_y_993_);
if (v___x_994_ == 0)
{
uint8_t v___x_995_; 
v___x_995_ = lean_uint64_dec_eq(v_x_992_, v_y_993_);
if (v___x_995_ == 0)
{
uint8_t v___x_996_; 
v___x_996_ = 2;
return v___x_996_;
}
else
{
uint8_t v___x_997_; 
v___x_997_ = 1;
return v___x_997_;
}
}
else
{
uint8_t v___x_998_; 
v___x_998_ = 0;
return v___x_998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__0___boxed(lean_object* v_x_999_, lean_object* v_y_1000_){
_start:
{
uint64_t v_x_boxed_1001_; uint64_t v_y_boxed_1002_; uint8_t v_res_1003_; lean_object* v_r_1004_; 
v_x_boxed_1001_ = lean_unbox_uint64(v_x_999_);
lean_dec_ref(v_x_999_);
v_y_boxed_1002_ = lean_unbox_uint64(v_y_1000_);
lean_dec_ref(v_y_1000_);
v_res_1003_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__0(v_x_boxed_1001_, v_y_boxed_1002_);
v_r_1004_ = lean_box(v_res_1003_);
return v_r_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__1(lean_object* v_expireTime_1005_, lean_object* v_x_1006_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v_x_1006_);
lean_ctor_set(v___x_1007_, 1, v_expireTime_1005_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__2(lean_object* v_val_1009_, lean_object* v_inst_1010_, lean_object* v_x_1011_, lean_object* v___y_1012_){
_start:
{
if (lean_obj_tag(v_x_1011_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec_ref(v_inst_1010_);
v_a_1014_ = lean_ctor_get(v_x_1011_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_x_1011_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v_x_1011_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v_x_1011_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
lean_ctor_set_tag(v___x_1016_, 1);
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1040_; 
v_a_1022_ = lean_ctor_get(v_x_1011_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_x_1011_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1024_ = v_x_1011_;
v_isShared_1025_ = v_isSharedCheck_1040_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v_x_1011_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1040_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v_rpcEncode_1027_; lean_object* v_objects_1028_; lean_object* v_expireTime_1029_; lean_object* v___f_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v_fst_1034_; lean_object* v_snd_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1026_ = lean_st_ref_take(v_val_1009_);
v_rpcEncode_1027_ = lean_ctor_get(v_inst_1010_, 0);
lean_inc_ref(v_rpcEncode_1027_);
lean_dec_ref(v_inst_1010_);
v_objects_1028_ = lean_ctor_get(v___x_1026_, 0);
lean_inc_ref(v_objects_1028_);
v_expireTime_1029_ = lean_ctor_get(v___x_1026_, 1);
lean_inc(v_expireTime_1029_);
lean_dec(v___x_1026_);
v___f_1030_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1030_, 0, v_expireTime_1029_);
v___x_1031_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__2___closed__0));
v___x_1032_ = lean_apply_2(v_rpcEncode_1027_, v_a_1022_, v_objects_1028_);
v___x_1033_ = l_Prod_map___redArg(v___x_1031_, v___f_1030_, v___x_1032_);
v_fst_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_fst_1034_);
v_snd_1035_ = lean_ctor_get(v___x_1033_, 1);
lean_inc(v_snd_1035_);
lean_dec_ref(v___x_1033_);
v___x_1036_ = lean_st_ref_put(v_val_1009_, v_snd_1035_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set_tag(v___x_1024_, 0);
lean_ctor_set(v___x_1024_, 0, v_fst_1034_);
v___x_1038_ = v___x_1024_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_fst_1034_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__2___boxed(lean_object* v_val_1041_, lean_object* v_inst_1042_, lean_object* v_x_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__2(v_val_1041_, v_inst_1042_, v_x_1043_, v___y_1044_);
lean_dec_ref(v___y_1044_);
lean_dec(v_val_1041_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__3(lean_object* v___f_1054_, lean_object* v_inst_1055_, lean_object* v_inst_1056_, lean_object* v_method_1057_, lean_object* v_handler_1058_, uint64_t v_seshId_1059_, lean_object* v_j_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_rpcSessions_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v_rpcSessions_1063_ = lean_ctor_get(v___y_1061_, 0);
v___x_1064_ = lean_box_uint64(v_seshId_1059_);
lean_inc(v_rpcSessions_1063_);
v___x_1065_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_1054_, v_rpcSessions_1063_, v___x_1064_);
if (lean_obj_tag(v___x_1065_) == 1)
{
lean_object* v_val_1066_; lean_object* v___f_1067_; lean_object* v___x_1068_; lean_object* v_rpcDecode_1069_; lean_object* v_objects_1070_; lean_object* v___x_1071_; 
v_val_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc_n(v_val_1066_, 2);
lean_dec_ref_known(v___x_1065_, 1);
v___f_1067_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_1067_, 0, v_val_1066_);
lean_closure_set(v___f_1067_, 1, v_inst_1055_);
v___x_1068_ = lean_st_ref_get(v_val_1066_);
lean_dec(v_val_1066_);
v_rpcDecode_1069_ = lean_ctor_get(v_inst_1056_, 1);
lean_inc_ref(v_rpcDecode_1069_);
lean_dec_ref(v_inst_1056_);
v_objects_1070_ = lean_ctor_get(v___x_1068_, 0);
lean_inc_ref(v_objects_1070_);
lean_dec(v___x_1068_);
lean_inc(v_j_1060_);
v___x_1071_ = lean_apply_2(v_rpcDecode_1069_, v_j_1060_, v_objects_1070_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1092_; 
lean_dec_ref(v___f_1067_);
lean_dec_ref(v_handler_1058_);
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1074_ = v___x_1071_;
v_isShared_1075_ = v_isSharedCheck_1092_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1071_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1092_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
uint8_t v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1076_ = 3;
v___x_1077_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__0));
v___x_1078_ = 1;
v___x_1079_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_1057_, v___x_1078_);
v___x_1080_ = lean_string_append(v___x_1077_, v___x_1079_);
lean_dec_ref(v___x_1079_);
v___x_1081_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__1));
v___x_1082_ = lean_string_append(v___x_1080_, v___x_1081_);
v___x_1083_ = l_Lean_Json_compress(v_j_1060_);
v___x_1084_ = lean_string_append(v___x_1082_, v___x_1083_);
lean_dec_ref(v___x_1083_);
v___x_1085_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__2));
v___x_1086_ = lean_string_append(v___x_1084_, v___x_1085_);
v___x_1087_ = lean_string_append(v___x_1086_, v_a_1072_);
lean_dec(v_a_1072_);
v___x_1088_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set_uint8(v___x_1088_, sizeof(void*)*1, v___x_1076_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set_tag(v___x_1074_, 1);
lean_ctor_set(v___x_1074_, 0, v___x_1088_);
v___x_1090_ = v___x_1074_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1094_; 
lean_dec(v_j_1060_);
lean_dec(v_method_1057_);
v_a_1093_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1071_, 1);
lean_inc_ref(v___y_1061_);
v___x_1094_ = lean_apply_3(v_handler_1058_, v_a_1093_, v___y_1061_, lean_box(0));
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1096_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___x_1094_, 1);
v___x_1096_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_a_1095_, v___f_1067_, v___y_1061_);
return v___x_1096_;
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec_ref(v___f_1067_);
v_a_1097_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1094_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1094_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
}
else
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_dec(v___x_1065_);
lean_dec(v_j_1060_);
lean_dec_ref(v_handler_1058_);
lean_dec(v_method_1057_);
lean_dec_ref(v_inst_1056_);
lean_dec_ref(v_inst_1055_);
v___x_1105_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__4));
v___x_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
return v___x_1106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__3___boxed(lean_object* v___f_1107_, lean_object* v_inst_1108_, lean_object* v_inst_1109_, lean_object* v_method_1110_, lean_object* v_handler_1111_, lean_object* v_seshId_1112_, lean_object* v_j_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
uint64_t v_seshId_boxed_1116_; lean_object* v_res_1117_; 
v_seshId_boxed_1116_ = lean_unbox_uint64(v_seshId_1112_);
lean_dec_ref(v_seshId_1112_);
v_res_1117_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__3(v___f_1107_, v_inst_1108_, v_inst_1109_, v_method_1110_, v_handler_1111_, v_seshId_boxed_1116_, v_j_1113_, v___y_1114_);
lean_dec_ref(v___y_1114_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg(lean_object* v_method_1119_, lean_object* v_inst_1120_, lean_object* v_inst_1121_, lean_object* v_handler_1122_){
_start:
{
lean_object* v___f_1123_; lean_object* v___f_1124_; 
v___f_1123_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___closed__0));
v___f_1124_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___boxed), 9, 5);
lean_closure_set(v___f_1124_, 0, v___f_1123_);
lean_closure_set(v___f_1124_, 1, v_inst_1121_);
lean_closure_set(v___f_1124_, 2, v_inst_1120_);
lean_closure_set(v___f_1124_, 3, v_method_1119_);
lean_closure_set(v___f_1124_, 4, v_handler_1122_);
return v___f_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure(lean_object* v_method_1125_, lean_object* v_paramType_1126_, lean_object* v_respType_1127_, lean_object* v_inst_1128_, lean_object* v_inst_1129_, lean_object* v_handler_1130_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_Server_wrapRpcProcedure___redArg(v_method_1125_, v_inst_1128_, v_inst_1129_, v_handler_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg(lean_object* v_method_1138_, lean_object* v_inst_1139_, lean_object* v_inst_1140_, lean_object* v_handler_1141_){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v_errMsg_1150_; uint8_t v___x_1151_; 
v___x_1143_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__0));
v___x_1144_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__1));
v___x_1145_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__2));
v___x_1146_ = 1;
lean_inc(v_method_1138_);
v___x_1147_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_1138_, v___x_1146_);
v___x_1148_ = lean_string_append(v___x_1145_, v___x_1147_);
lean_dec_ref(v___x_1147_);
v___x_1149_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__3));
v_errMsg_1150_ = lean_string_append(v___x_1148_, v___x_1149_);
v___x_1151_ = l_Lean_initializing();
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec_ref(v_handler_1141_);
lean_dec_ref(v_inst_1140_);
lean_dec_ref(v_inst_1139_);
lean_dec(v_method_1138_);
v___x_1152_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__4));
v___x_1153_ = lean_string_append(v_errMsg_1150_, v___x_1152_);
v___x_1154_ = lean_mk_io_user_error(v___x_1153_);
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
return v___x_1155_;
}
else
{
lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1156_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_1157_ = lean_st_ref_get(v___x_1156_);
lean_inc(v_method_1138_);
v___x_1158_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1143_, v___x_1144_, v___x_1157_, v_method_1138_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
lean_dec_ref(v_errMsg_1150_);
lean_inc(v_method_1138_);
v___x_1159_ = l_Lean_Server_wrapRpcProcedure___redArg(v_method_1138_, v_inst_1139_, v_inst_1140_, v_handler_1141_);
v___x_1160_ = lean_st_ref_take(v___x_1156_);
v___x_1161_ = l_Lean_PersistentHashMap_insert___redArg(v___x_1143_, v___x_1144_, v___x_1160_, v_method_1138_, v___x_1159_);
v___x_1162_ = lean_st_ref_put(v___x_1156_, v___x_1161_);
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
return v___x_1163_;
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
lean_dec_ref(v_handler_1141_);
lean_dec_ref(v_inst_1140_);
lean_dec_ref(v_inst_1139_);
lean_dec(v_method_1138_);
v___x_1164_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__5));
v___x_1165_ = lean_string_append(v_errMsg_1150_, v___x_1164_);
v___x_1166_ = lean_mk_io_user_error(v___x_1165_);
v___x_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
return v___x_1167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg___boxed(lean_object* v_method_1168_, lean_object* v_inst_1169_, lean_object* v_inst_1170_, lean_object* v_handler_1171_, lean_object* v_a_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_Server_registerBuiltinRpcProcedure___redArg(v_method_1168_, v_inst_1169_, v_inst_1170_, v_handler_1171_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure(lean_object* v_method_1174_, lean_object* v_paramType_1175_, lean_object* v_respType_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v_handler_1179_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_Server_registerBuiltinRpcProcedure___redArg(v_method_1174_, v_inst_1177_, v_inst_1178_, v_handler_1179_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___boxed(lean_object* v_method_1182_, lean_object* v_paramType_1183_, lean_object* v_respType_1184_, lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_handler_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_Server_registerBuiltinRpcProcedure(v_method_1182_, v_paramType_1183_, v_respType_1184_, v_inst_1185_, v_inst_1186_, v_handler_1187_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(lean_object* v_e_1190_, lean_object* v___y_1191_){
_start:
{
uint8_t v___x_1193_; 
v___x_1193_ = l_Lean_Expr_hasMVar(v_e_1190_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v_e_1190_);
return v___x_1194_;
}
else
{
lean_object* v___x_1195_; lean_object* v_mctx_1196_; lean_object* v___x_1197_; lean_object* v_fst_1198_; lean_object* v_snd_1199_; lean_object* v___x_1200_; lean_object* v_cache_1201_; lean_object* v_zetaDeltaFVarIds_1202_; lean_object* v_postponed_1203_; lean_object* v_diag_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1213_; 
v___x_1195_ = lean_st_ref_get(v___y_1191_);
v_mctx_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc_ref(v_mctx_1196_);
lean_dec(v___x_1195_);
v___x_1197_ = l_Lean_instantiateMVarsCore(v_mctx_1196_, v_e_1190_);
v_fst_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_fst_1198_);
v_snd_1199_ = lean_ctor_get(v___x_1197_, 1);
lean_inc(v_snd_1199_);
lean_dec_ref(v___x_1197_);
v___x_1200_ = lean_st_ref_take(v___y_1191_);
v_cache_1201_ = lean_ctor_get(v___x_1200_, 1);
v_zetaDeltaFVarIds_1202_ = lean_ctor_get(v___x_1200_, 2);
v_postponed_1203_ = lean_ctor_get(v___x_1200_, 3);
v_diag_1204_ = lean_ctor_get(v___x_1200_, 4);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; 
v_unused_1214_ = lean_ctor_get(v___x_1200_, 0);
lean_dec(v_unused_1214_);
v___x_1206_ = v___x_1200_;
v_isShared_1207_ = v_isSharedCheck_1213_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_diag_1204_);
lean_inc(v_postponed_1203_);
lean_inc(v_zetaDeltaFVarIds_1202_);
lean_inc(v_cache_1201_);
lean_dec(v___x_1200_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1213_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v_snd_1199_);
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_snd_1199_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_cache_1201_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_zetaDeltaFVarIds_1202_);
lean_ctor_set(v_reuseFailAlloc_1212_, 3, v_postponed_1203_);
lean_ctor_set(v_reuseFailAlloc_1212_, 4, v_diag_1204_);
v___x_1209_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_st_ref_put(v___y_1191_, v___x_1209_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v_fst_1198_);
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg___boxed(lean_object* v_e_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(v_e_1215_, v___y_1216_);
lean_dec(v___y_1216_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0(lean_object* v_e_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(v_e_1219_, v___y_1223_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___boxed(lean_object* v_e_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0(v_e_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg(lean_object* v_a_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg___boxed(lean_object* v_a_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg(v_a_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1(lean_object* v_00_u03b1_1255_, lean_object* v_a_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___boxed(lean_object* v_00_u03b1_1265_, lean_object* v_a_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1(v_00_u03b1_1265_, v_a_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
return v_res_1274_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_);
v___x_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
return v___x_1276_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3___redArg___closed__0);
v___x_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(lean_object* v_env_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; lean_object* v_nextMacroScope_1283_; lean_object* v_ngen_1284_; lean_object* v_auxDeclNGen_1285_; lean_object* v_traceState_1286_; lean_object* v_recordedDeps_1287_; lean_object* v_messages_1288_; lean_object* v_infoState_1289_; lean_object* v_snapshotTasks_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1301_; 
v___x_1282_ = lean_st_ref_take(v___y_1280_);
v_nextMacroScope_1283_ = lean_ctor_get(v___x_1282_, 1);
v_ngen_1284_ = lean_ctor_get(v___x_1282_, 2);
v_auxDeclNGen_1285_ = lean_ctor_get(v___x_1282_, 3);
v_traceState_1286_ = lean_ctor_get(v___x_1282_, 4);
v_recordedDeps_1287_ = lean_ctor_get(v___x_1282_, 6);
v_messages_1288_ = lean_ctor_get(v___x_1282_, 7);
v_infoState_1289_ = lean_ctor_get(v___x_1282_, 8);
v_snapshotTasks_1290_ = lean_ctor_get(v___x_1282_, 9);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1301_ == 0)
{
lean_object* v_unused_1302_; lean_object* v_unused_1303_; 
v_unused_1302_ = lean_ctor_get(v___x_1282_, 5);
lean_dec(v_unused_1302_);
v_unused_1303_ = lean_ctor_get(v___x_1282_, 0);
lean_dec(v_unused_1303_);
v___x_1292_ = v___x_1282_;
v_isShared_1293_ = v_isSharedCheck_1301_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_snapshotTasks_1290_);
lean_inc(v_infoState_1289_);
lean_inc(v_messages_1288_);
lean_inc(v_recordedDeps_1287_);
lean_inc(v_traceState_1286_);
lean_inc(v_auxDeclNGen_1285_);
lean_inc(v_ngen_1284_);
lean_inc(v_nextMacroScope_1283_);
lean_dec(v___x_1282_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1301_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1297_; 
v___x_1294_ = lean_box(0);
v___x_1295_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3___redArg___closed__1);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 5, v___x_1295_);
lean_ctor_set(v___x_1292_, 0, v_env_1279_);
v___x_1297_ = v___x_1292_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_env_1279_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v_nextMacroScope_1283_);
lean_ctor_set(v_reuseFailAlloc_1300_, 2, v_ngen_1284_);
lean_ctor_set(v_reuseFailAlloc_1300_, 3, v_auxDeclNGen_1285_);
lean_ctor_set(v_reuseFailAlloc_1300_, 4, v_traceState_1286_);
lean_ctor_set(v_reuseFailAlloc_1300_, 5, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1300_, 6, v_recordedDeps_1287_);
lean_ctor_set(v_reuseFailAlloc_1300_, 7, v_messages_1288_);
lean_ctor_set(v_reuseFailAlloc_1300_, 8, v_infoState_1289_);
lean_ctor_set(v_reuseFailAlloc_1300_, 9, v_snapshotTasks_1290_);
v___x_1297_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = lean_st_ref_put(v___y_1280_, v___x_1297_);
v___x_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1294_);
return v___x_1299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3___redArg___boxed(lean_object* v_env_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v_env_1304_, v___y_1305_);
lean_dec(v___y_1305_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3(lean_object* v_env_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v_env_1308_, v___y_1310_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3___boxed(lean_object* v_env_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3(v_env_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
return v_res_1317_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_registerRpcProcedure___lam__0(lean_object* v_x_1318_){
_start:
{
uint8_t v___x_1319_; 
v___x_1319_ = 0;
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__0___boxed(lean_object* v_x_1320_){
_start:
{
uint8_t v_res_1321_; lean_object* v_r_1322_; 
v_res_1321_ = l_Lean_Server_registerRpcProcedure___lam__0(v_x_1320_);
lean_dec(v_x_1320_);
v_r_1322_ = lean_box(v_res_1321_);
return v_r_1322_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__3));
v___x_1328_ = l_String_toRawSubstring_x27(v___x_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__1(lean_object* v___x_1339_, lean_object* v___x_1340_, lean_object* v_method_1341_, lean_object* v___x_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_toCold_1350_; lean_object* v_ref_1351_; lean_object* v_quotContext_1352_; lean_object* v_currMacroScope_1353_; uint8_t v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___y_1373_; lean_object* v___x_1387_; 
v_toCold_1350_ = lean_ctor_get(v___y_1347_, 0);
v_ref_1351_ = lean_ctor_get(v___y_1347_, 2);
v_quotContext_1352_ = lean_ctor_get(v_toCold_1350_, 8);
v_currMacroScope_1353_ = lean_ctor_get(v_toCold_1350_, 9);
v___x_1354_ = 0;
v___x_1355_ = l_Lean_SourceInfo_fromRef(v_ref_1351_, v___x_1354_);
v___x_1356_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__0));
v___x_1357_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__1));
v___x_1358_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__2));
lean_inc_ref_n(v___x_1339_, 2);
v___x_1359_ = l_Lean_Name_mkStr4(v___x_1339_, v___x_1356_, v___x_1357_, v___x_1358_);
v___x_1360_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__3));
v___x_1361_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___lam__1___closed__4, &l_Lean_Server_registerRpcProcedure___lam__1___closed__4_once, _init_l_Lean_Server_registerRpcProcedure___lam__1___closed__4);
v___x_1362_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__5));
lean_inc(v_currMacroScope_1353_);
lean_inc(v_quotContext_1352_);
v___x_1363_ = l_Lean_addMacroScope(v_quotContext_1352_, v___x_1362_, v_currMacroScope_1353_);
v___x_1364_ = l_Lean_Name_mkStr3(v___x_1339_, v___x_1340_, v___x_1360_);
v___x_1365_ = lean_box(0);
lean_inc(v___x_1364_);
v___x_1366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1364_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1364_);
v___x_1368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
lean_ctor_set(v___x_1368_, 1, v___x_1365_);
v___x_1369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1366_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
lean_inc(v___x_1355_);
v___x_1370_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1355_);
lean_ctor_set(v___x_1370_, 1, v___x_1361_);
lean_ctor_set(v___x_1370_, 2, v___x_1363_);
lean_ctor_set(v___x_1370_, 3, v___x_1369_);
v___x_1371_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__7));
lean_inc(v_method_1341_);
v___x_1387_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_1365_, v_method_1341_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v___x_1388_; 
lean_inc(v_method_1341_);
v___x_1388_ = l_Lean_quoteNameMk(v_method_1341_);
v___y_1373_ = v___x_1388_;
goto v___jp_1372_;
}
else
{
lean_object* v_val_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v_val_1389_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_val_1389_);
lean_dec_ref_known(v___x_1387_, 1);
v___x_1390_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__10));
lean_inc_ref(v___x_1339_);
v___x_1391_ = l_Lean_Name_mkStr4(v___x_1339_, v___x_1356_, v___x_1357_, v___x_1390_);
v___x_1392_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__11));
v___x_1393_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__12));
v___x_1394_ = lean_string_intercalate(v___x_1393_, v_val_1389_);
v___x_1395_ = lean_string_append(v___x_1392_, v___x_1394_);
lean_dec_ref(v___x_1394_);
v___x_1396_ = lean_box(2);
v___x_1397_ = l_Lean_Syntax_mkNameLit(v___x_1395_, v___x_1396_);
v___x_1398_ = lean_unsigned_to_nat(1u);
v___x_1399_ = lean_mk_empty_array_with_capacity(v___x_1398_);
v___x_1400_ = lean_array_push(v___x_1399_, v___x_1397_);
v___x_1401_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1396_);
lean_ctor_set(v___x_1401_, 1, v___x_1391_);
lean_ctor_set(v___x_1401_, 2, v___x_1400_);
v___y_1373_ = v___x_1401_;
goto v___jp_1372_;
}
v___jp_1372_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; lean_object* v___x_1384_; 
v___x_1374_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__8));
v___x_1375_ = l_Lean_Name_mkStr4(v___x_1339_, v___x_1356_, v___x_1357_, v___x_1374_);
v___x_1376_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__9));
lean_inc_n(v___x_1355_, 3);
v___x_1377_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1355_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v___x_1378_ = l_Lean_Syntax_node1(v___x_1355_, v___x_1375_, v___x_1377_);
v___x_1379_ = l_Lean_mkIdent(v_method_1341_);
lean_inc(v___x_1378_);
v___x_1380_ = l_Lean_Syntax_node4(v___x_1355_, v___x_1371_, v___y_1373_, v___x_1378_, v___x_1378_, v___x_1379_);
v___x_1381_ = l_Lean_Syntax_node2(v___x_1355_, v___x_1359_, v___x_1370_, v___x_1380_);
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1342_);
v___x_1383_ = 1;
v___x_1384_ = l_Lean_Elab_Term_elabTerm(v___x_1381_, v___x_1382_, v___x_1383_, v___x_1383_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec_ref(v___y_1347_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v___x_1386_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(v_a_1385_, v___y_1346_);
return v___x_1386_;
}
else
{
return v___x_1384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__1___boxed(lean_object* v___x_1402_, lean_object* v___x_1403_, lean_object* v_method_1404_, lean_object* v___x_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_Server_registerRpcProcedure___lam__1(v___x_1402_, v___x_1403_, v_method_1404_, v___x_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
return v_res_1413_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Server_registerRpcProcedure_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_);
v___x_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Server_registerRpcProcedure_spec__2_spec__2___redArg(){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Server_registerRpcProcedure_spec__2_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Server_registerRpcProcedure_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Server_registerRpcProcedure_spec__2_spec__2___redArg___closed__0);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Server_registerRpcProcedure_spec__2_spec__2___redArg___boxed(lean_object* v___dummy_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Server_registerRpcProcedure_spec__2_spec__2___redArg();
return v_res_1419_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_);
v___x_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
return v___x_1421_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1422_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1423_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__0);
v___x_1424_ = lean_unsigned_to_nat(0u);
v___x_1425_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
lean_ctor_set(v___x_1425_, 2, v___x_1424_);
lean_ctor_set(v___x_1425_, 3, v___x_1424_);
lean_ctor_set(v___x_1425_, 4, v___x_1423_);
lean_ctor_set(v___x_1425_, 5, v___x_1423_);
lean_ctor_set(v___x_1425_, 6, v___x_1423_);
lean_ctor_set(v___x_1425_, 7, v___x_1423_);
lean_ctor_set(v___x_1425_, 8, v___x_1423_);
lean_ctor_set(v___x_1425_, 9, v___x_1423_);
lean_ctor_set(v___x_1425_, 10, v___x_1423_);
lean_ctor_set(v___x_1425_, 11, v___x_1422_);
return v___x_1425_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1426_ = lean_unsigned_to_nat(32u);
v___x_1427_ = lean_mk_empty_array_with_capacity(v___x_1426_);
v___x_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
return v___x_1428_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__3(void){
_start:
{
size_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1429_ = ((size_t)5ULL);
v___x_1430_ = lean_unsigned_to_nat(0u);
v___x_1431_ = lean_unsigned_to_nat(32u);
v___x_1432_ = lean_mk_empty_array_with_capacity(v___x_1431_);
v___x_1433_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__2);
v___x_1434_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
lean_ctor_set(v___x_1434_, 1, v___x_1432_);
lean_ctor_set(v___x_1434_, 2, v___x_1430_);
lean_ctor_set(v___x_1434_, 3, v___x_1430_);
lean_ctor_set_usize(v___x_1434_, 4, v___x_1429_);
return v___x_1434_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__4(void){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1435_ = lean_box(1);
v___x_1436_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__3);
v___x_1437_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__0);
v___x_1438_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
lean_ctor_set(v___x_1438_, 1, v___x_1436_);
lean_ctor_set(v___x_1438_, 2, v___x_1435_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5(lean_object* v_msgData_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v___x_1443_; lean_object* v_toCold_1444_; lean_object* v_env_1445_; lean_object* v_options_1446_; uint8_t v___x_1447_; lean_object* v_env_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1443_ = lean_st_ref_get(v___y_1441_);
v_toCold_1444_ = lean_ctor_get(v___y_1440_, 0);
v_env_1445_ = lean_ctor_get(v___x_1443_, 0);
lean_inc_ref(v_env_1445_);
lean_dec(v___x_1443_);
v_options_1446_ = lean_ctor_get(v_toCold_1444_, 2);
v___x_1447_ = 0;
v_env_1448_ = l_Lean_Environment_setRecordingDeps(v_env_1445_, v___x_1447_);
v___x_1449_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__1);
v___x_1450_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__4);
lean_inc_ref(v_options_1446_);
v___x_1451_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1451_, 0, v_env_1448_);
lean_ctor_set(v___x_1451_, 1, v___x_1449_);
lean_ctor_set(v___x_1451_, 2, v___x_1450_);
lean_ctor_set(v___x_1451_, 3, v_options_1446_);
v___x_1452_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
lean_ctor_set(v___x_1452_, 1, v_msgData_1439_);
v___x_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___boxed(lean_object* v_msgData_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5(v_msgData_1454_, v___y_1455_, v___y_1456_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4___redArg(lean_object* v_msg_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_ref_1463_; lean_object* v___x_1464_; lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1473_; 
v_ref_1463_ = lean_ctor_get(v___y_1460_, 2);
v___x_1464_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5(v_msg_1459_, v___y_1460_, v___y_1461_);
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1467_ = v___x_1464_;
v_isShared_1468_ = v_isSharedCheck_1473_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1473_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; lean_object* v___x_1471_; 
lean_inc(v_ref_1463_);
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v_ref_1463_);
lean_ctor_set(v___x_1469_, 1, v_a_1465_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set_tag(v___x_1467_, 1);
lean_ctor_set(v___x_1467_, 0, v___x_1469_);
v___x_1471_ = v___x_1467_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4___redArg___boxed(lean_object* v_msg_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4___redArg(v_msg_1474_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
return v_res_1478_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__3(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1483_ = lean_box(0);
v___x_1484_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1));
v___x_1485_ = l_Lean_mkConst(v___x_1484_, v___x_1483_);
return v___x_1485_;
}
}
static uint64_t _init_l_Lean_Server_registerRpcProcedure___closed__8(void){
_start:
{
lean_object* v___x_1505_; uint64_t v___x_1506_; 
v___x_1505_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__7));
v___x_1506_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1505_);
return v___x_1506_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__9(void){
_start:
{
uint64_t v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = lean_uint64_once(&l_Lean_Server_registerRpcProcedure___closed__8, &l_Lean_Server_registerRpcProcedure___closed__8_once, _init_l_Lean_Server_registerRpcProcedure___closed__8);
v___x_1508_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__7));
v___x_1509_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
lean_ctor_set_uint64(v___x_1509_, sizeof(void*)*1, v___x_1507_);
return v___x_1509_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__10(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_);
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
return v___x_1511_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__11(void){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1512_ = lean_box(1);
v___x_1513_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__3);
v___x_1514_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__10, &l_Lean_Server_registerRpcProcedure___closed__10_once, _init_l_Lean_Server_registerRpcProcedure___closed__10);
v___x_1515_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
lean_ctor_set(v___x_1515_, 1, v___x_1513_);
lean_ctor_set(v___x_1515_, 2, v___x_1512_);
return v___x_1515_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__12(void){
_start:
{
uint8_t v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; uint8_t v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1516_ = 1;
v___x_1517_ = lean_unsigned_to_nat(0u);
v___x_1518_ = lean_box(0);
v___x_1519_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__4));
v___x_1520_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__11, &l_Lean_Server_registerRpcProcedure___closed__11_once, _init_l_Lean_Server_registerRpcProcedure___closed__11);
v___x_1521_ = lean_box(1);
v___x_1522_ = 0;
v___x_1523_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__9, &l_Lean_Server_registerRpcProcedure___closed__9_once, _init_l_Lean_Server_registerRpcProcedure___closed__9);
v___x_1524_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
lean_ctor_set(v___x_1524_, 1, v___x_1521_);
lean_ctor_set(v___x_1524_, 2, v___x_1520_);
lean_ctor_set(v___x_1524_, 3, v___x_1519_);
lean_ctor_set(v___x_1524_, 4, v___x_1518_);
lean_ctor_set(v___x_1524_, 5, v___x_1517_);
lean_ctor_set(v___x_1524_, 6, v___x_1518_);
lean_ctor_set_uint8(v___x_1524_, sizeof(void*)*7, v___x_1522_);
lean_ctor_set_uint8(v___x_1524_, sizeof(void*)*7 + 1, v___x_1522_);
lean_ctor_set_uint8(v___x_1524_, sizeof(void*)*7 + 2, v___x_1522_);
lean_ctor_set_uint8(v___x_1524_, sizeof(void*)*7 + 3, v___x_1516_);
return v___x_1524_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__13(void){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1525_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1526_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__10, &l_Lean_Server_registerRpcProcedure___closed__10_once, _init_l_Lean_Server_registerRpcProcedure___closed__10);
v___x_1527_ = lean_unsigned_to_nat(0u);
v___x_1528_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
lean_ctor_set(v___x_1528_, 2, v___x_1527_);
lean_ctor_set(v___x_1528_, 3, v___x_1527_);
lean_ctor_set(v___x_1528_, 4, v___x_1526_);
lean_ctor_set(v___x_1528_, 5, v___x_1526_);
lean_ctor_set(v___x_1528_, 6, v___x_1526_);
lean_ctor_set(v___x_1528_, 7, v___x_1526_);
lean_ctor_set(v___x_1528_, 8, v___x_1526_);
lean_ctor_set(v___x_1528_, 9, v___x_1526_);
lean_ctor_set(v___x_1528_, 10, v___x_1526_);
lean_ctor_set(v___x_1528_, 11, v___x_1525_);
return v___x_1528_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__14(void){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Server_registerRpcProcedure_spec__2_spec__2___redArg();
return v___x_1529_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__15(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1530_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__10, &l_Lean_Server_registerRpcProcedure___closed__10_once, _init_l_Lean_Server_registerRpcProcedure___closed__10);
v___x_1531_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__14, &l_Lean_Server_registerRpcProcedure___closed__14_once, _init_l_Lean_Server_registerRpcProcedure___closed__14);
v___x_1532_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
lean_ctor_set(v___x_1532_, 1, v___x_1530_);
lean_ctor_set(v___x_1532_, 2, v___x_1530_);
lean_ctor_set(v___x_1532_, 3, v___x_1530_);
lean_ctor_set(v___x_1532_, 4, v___x_1530_);
lean_ctor_set(v___x_1532_, 5, v___x_1530_);
lean_ctor_set(v___x_1532_, 6, v___x_1530_);
return v___x_1532_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__16(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__10, &l_Lean_Server_registerRpcProcedure___closed__10_once, _init_l_Lean_Server_registerRpcProcedure___closed__10);
v___x_1534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
lean_ctor_set(v___x_1534_, 2, v___x_1533_);
lean_ctor_set(v___x_1534_, 3, v___x_1533_);
lean_ctor_set(v___x_1534_, 4, v___x_1533_);
return v___x_1534_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__17(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1535_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__16, &l_Lean_Server_registerRpcProcedure___closed__16_once, _init_l_Lean_Server_registerRpcProcedure___closed__16);
v___x_1536_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4_spec__5___closed__3);
v___x_1537_ = lean_box(1);
v___x_1538_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__15, &l_Lean_Server_registerRpcProcedure___closed__15_once, _init_l_Lean_Server_registerRpcProcedure___closed__15);
v___x_1539_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__13, &l_Lean_Server_registerRpcProcedure___closed__13_once, _init_l_Lean_Server_registerRpcProcedure___closed__13);
v___x_1540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
lean_ctor_set(v___x_1540_, 1, v___x_1538_);
lean_ctor_set(v___x_1540_, 2, v___x_1537_);
lean_ctor_set(v___x_1540_, 3, v___x_1536_);
lean_ctor_set(v___x_1540_, 4, v___x_1535_);
return v___x_1540_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__18(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__10, &l_Lean_Server_registerRpcProcedure___closed__10_once, _init_l_Lean_Server_registerRpcProcedure___closed__10);
v___x_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
return v___x_1542_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__20(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__19));
v___x_1545_ = l_Lean_stringToMessageData(v___x_1544_);
return v___x_1545_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__21(void){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__3));
v___x_1547_ = l_Lean_stringToMessageData(v___x_1546_);
return v___x_1547_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__22(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__5));
v___x_1549_ = l_Lean_stringToMessageData(v___x_1548_);
return v___x_1549_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__24(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__23));
v___x_1552_ = l_Lean_stringToMessageData(v___x_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure(lean_object* v_method_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___x_1628_; lean_object* v_env_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1628_ = lean_st_ref_get(v_a_1555_);
v_env_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc_ref(v_env_1629_);
lean_dec(v___x_1628_);
v___x_1630_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__20, &l_Lean_Server_registerRpcProcedure___closed__20_once, _init_l_Lean_Server_registerRpcProcedure___closed__20);
lean_inc(v_method_1553_);
v___x_1631_ = l_Lean_MessageData_ofName(v_method_1553_);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__21, &l_Lean_Server_registerRpcProcedure___closed__21_once, _init_l_Lean_Server_registerRpcProcedure___closed__21);
v___x_1634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1632_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1645_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_1646_ = lean_st_ref_get(v___x_1645_);
v___x_1647_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(v___x_1646_, v_method_1553_);
lean_dec(v___x_1646_);
if (v___x_1647_ == 0)
{
v___y_1636_ = v_a_1554_;
v___y_1637_ = v_a_1555_;
goto v___jp_1635_;
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_dec_ref(v_env_1629_);
lean_dec(v_method_1553_);
v___x_1648_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__24, &l_Lean_Server_registerRpcProcedure___closed__24_once, _init_l_Lean_Server_registerRpcProcedure___closed__24);
v___x_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1634_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4___redArg(v___x_1649_, v_a_1554_, v_a_1555_);
return v___x_1650_;
}
v___jp_1557_:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___f_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; uint8_t v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1560_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__2));
lean_inc_n(v_method_1553_, 2);
v___x_1561_ = l_Lean_Name_append(v_method_1553_, v___x_1560_);
v___x_1562_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_1563_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_1564_ = lean_box(0);
v___x_1565_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__3, &l_Lean_Server_registerRpcProcedure___closed__3_once, _init_l_Lean_Server_registerRpcProcedure___closed__3);
v___f_1566_ = lean_alloc_closure((void*)(l_Lean_Server_registerRpcProcedure___lam__1___boxed), 11, 4);
lean_closure_set(v___f_1566_, 0, v___x_1562_);
lean_closure_set(v___f_1566_, 1, v___x_1563_);
lean_closure_set(v___f_1566_, 2, v_method_1553_);
lean_closure_set(v___f_1566_, 3, v___x_1565_);
v___x_1567_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___boxed), 9, 2);
lean_closure_set(v___x_1567_, 0, lean_box(0));
lean_closure_set(v___x_1567_, 1, v___f_1566_);
v___x_1568_ = 1;
v___x_1569_ = 0;
v___x_1570_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__5));
v___x_1571_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__6));
v___x_1572_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__12, &l_Lean_Server_registerRpcProcedure___closed__12_once, _init_l_Lean_Server_registerRpcProcedure___closed__12);
v___x_1573_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__17, &l_Lean_Server_registerRpcProcedure___closed__17_once, _init_l_Lean_Server_registerRpcProcedure___closed__17);
v___x_1574_ = lean_st_mk_ref(v___x_1573_);
v___x_1575_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_1567_, v___x_1570_, v___x_1571_, v___x_1572_, v___x_1574_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v_fst_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1618_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1575_, 1);
v_fst_1577_ = lean_ctor_get(v_a_1576_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v_a_1576_);
if (v_isSharedCheck_1618_ == 0)
{
lean_object* v_unused_1619_; 
v_unused_1619_ = lean_ctor_get(v_a_1576_, 1);
lean_dec(v_unused_1619_);
v___x_1579_ = v_a_1576_;
v_isShared_1580_ = v_isSharedCheck_1618_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_fst_1577_);
lean_dec(v_a_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1618_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; lean_object* v___x_1586_; 
v___x_1581_ = lean_st_ref_get(v___x_1574_);
lean_dec(v___x_1574_);
lean_dec(v___x_1581_);
lean_inc_n(v___x_1561_, 2);
v___x_1582_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1561_);
lean_ctor_set(v___x_1582_, 1, v___x_1564_);
lean_ctor_set(v___x_1582_, 2, v___x_1565_);
v___x_1583_ = lean_box(0);
v___x_1584_ = 1;
if (v_isShared_1580_ == 0)
{
lean_ctor_set_tag(v___x_1579_, 1);
lean_ctor_set(v___x_1579_, 1, v___x_1564_);
lean_ctor_set(v___x_1579_, 0, v___x_1561_);
v___x_1586_ = v___x_1579_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1561_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v___x_1564_);
v___x_1586_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1587_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1587_, 0, v___x_1582_);
lean_ctor_set(v___x_1587_, 1, v_fst_1577_);
lean_ctor_set(v___x_1587_, 2, v___x_1583_);
lean_ctor_set(v___x_1587_, 3, v___x_1586_);
lean_ctor_set_uint8(v___x_1587_, sizeof(void*)*4, v___x_1584_);
v___x_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
lean_inc_ref(v___x_1588_);
v___x_1589_ = l_Lean_addDecl(v___x_1588_, v___x_1569_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v___x_1590_; lean_object* v_env_1591_; lean_object* v_nextMacroScope_1592_; lean_object* v_ngen_1593_; lean_object* v_auxDeclNGen_1594_; lean_object* v_traceState_1595_; lean_object* v_recordedDeps_1596_; lean_object* v_messages_1597_; lean_object* v_infoState_1598_; lean_object* v_snapshotTasks_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1615_; 
lean_dec_ref_known(v___x_1589_, 1);
v___x_1590_ = lean_st_ref_take(v___y_1559_);
v_env_1591_ = lean_ctor_get(v___x_1590_, 0);
v_nextMacroScope_1592_ = lean_ctor_get(v___x_1590_, 1);
v_ngen_1593_ = lean_ctor_get(v___x_1590_, 2);
v_auxDeclNGen_1594_ = lean_ctor_get(v___x_1590_, 3);
v_traceState_1595_ = lean_ctor_get(v___x_1590_, 4);
v_recordedDeps_1596_ = lean_ctor_get(v___x_1590_, 6);
v_messages_1597_ = lean_ctor_get(v___x_1590_, 7);
v_infoState_1598_ = lean_ctor_get(v___x_1590_, 8);
v_snapshotTasks_1599_ = lean_ctor_get(v___x_1590_, 9);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; 
v_unused_1616_ = lean_ctor_get(v___x_1590_, 5);
lean_dec(v_unused_1616_);
v___x_1601_ = v___x_1590_;
v_isShared_1602_ = v_isSharedCheck_1615_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_snapshotTasks_1599_);
lean_inc(v_infoState_1598_);
lean_inc(v_messages_1597_);
lean_inc(v_recordedDeps_1596_);
lean_inc(v_traceState_1595_);
lean_inc(v_auxDeclNGen_1594_);
lean_inc(v_ngen_1593_);
lean_inc(v_nextMacroScope_1592_);
lean_inc(v_env_1591_);
lean_dec(v___x_1590_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1615_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1606_; 
lean_inc(v___x_1561_);
v___x_1603_ = l_Lean_markMeta(v_env_1591_, v___x_1561_);
v___x_1604_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__18, &l_Lean_Server_registerRpcProcedure___closed__18_once, _init_l_Lean_Server_registerRpcProcedure___closed__18);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 5, v___x_1604_);
lean_ctor_set(v___x_1601_, 0, v___x_1603_);
v___x_1606_ = v___x_1601_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_nextMacroScope_1592_);
lean_ctor_set(v_reuseFailAlloc_1614_, 2, v_ngen_1593_);
lean_ctor_set(v_reuseFailAlloc_1614_, 3, v_auxDeclNGen_1594_);
lean_ctor_set(v_reuseFailAlloc_1614_, 4, v_traceState_1595_);
lean_ctor_set(v_reuseFailAlloc_1614_, 5, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1614_, 6, v_recordedDeps_1596_);
lean_ctor_set(v_reuseFailAlloc_1614_, 7, v_messages_1597_);
lean_ctor_set(v_reuseFailAlloc_1614_, 8, v_infoState_1598_);
lean_ctor_set(v_reuseFailAlloc_1614_, 9, v_snapshotTasks_1599_);
v___x_1606_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = lean_st_ref_put(v___y_1559_, v___x_1606_);
v___x_1608_ = l_Lean_compileDecl(v___x_1588_, v___x_1568_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v___x_1609_; lean_object* v_env_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
lean_dec_ref_known(v___x_1608_, 1);
v___x_1609_ = lean_st_ref_get(v___y_1559_);
v_env_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc_ref(v_env_1610_);
lean_dec(v___x_1609_);
v___x_1611_ = l_Lean_Server_userRpcProcedures;
v___x_1612_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1611_, v_env_1610_, v_method_1553_, v___x_1561_, v___x_1569_);
v___x_1613_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v___x_1612_, v___y_1559_);
return v___x_1613_;
}
else
{
lean_dec(v___x_1561_);
lean_dec(v_method_1553_);
return v___x_1608_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1588_, 1);
lean_dec(v___x_1561_);
lean_dec(v_method_1553_);
return v___x_1589_;
}
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec(v___x_1574_);
lean_dec(v___x_1561_);
lean_dec(v_method_1553_);
v_a_1620_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1575_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1575_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
v___jp_1635_:
{
lean_object* v___x_1638_; lean_object* v_toEnvExtension_1639_; lean_object* v_asyncMode_1640_; uint8_t v___x_1641_; 
v___x_1638_ = l_Lean_Server_userRpcProcedures;
v_toEnvExtension_1639_ = lean_ctor_get(v___x_1638_, 0);
v_asyncMode_1640_ = lean_ctor_get(v_toEnvExtension_1639_, 2);
lean_inc(v_method_1553_);
v___x_1641_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_1638_, v_env_1629_, v_method_1553_, v_asyncMode_1640_);
if (v___x_1641_ == 0)
{
lean_dec_ref_known(v___x_1634_, 2);
v___y_1558_ = v___y_1636_;
v___y_1559_ = v___y_1637_;
goto v___jp_1557_;
}
else
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_dec(v_method_1553_);
v___x_1642_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__22, &l_Lean_Server_registerRpcProcedure___closed__22_once, _init_l_Lean_Server_registerRpcProcedure___closed__22);
v___x_1643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1634_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4___redArg(v___x_1643_, v___y_1636_, v___y_1637_);
return v___x_1644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___boxed(lean_object* v_method_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_Server_registerRpcProcedure(v_method_1651_, v_a_1652_, v_a_1653_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Server_registerRpcProcedure_spec__2_spec__2(lean_object* v_00_u03b2_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__14, &l_Lean_Server_registerRpcProcedure___closed__14_once, _init_l_Lean_Server_registerRpcProcedure___closed__14);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__14, &l_Lean_Server_registerRpcProcedure___closed__14_once, _init_l_Lean_Server_registerRpcProcedure___closed__14);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___boxed(lean_object* v___dummy_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Server_registerRpcProcedure_spec__2___redArg();
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Server_registerRpcProcedure_spec__2(lean_object* v_00_u03b2_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__14, &l_Lean_Server_registerRpcProcedure___closed__14_once, _init_l_Lean_Server_registerRpcProcedure___closed__14);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4(lean_object* v_00_u03b1_1664_, lean_object* v_msg_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4___redArg(v_msg_1665_, v___y_1666_, v___y_1667_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4___boxed(lean_object* v_00_u03b1_1670_, lean_object* v_msg_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4(v_00_u03b1_1670_, v_msg_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(lean_object* v___x_1676_, lean_object* v_decl_1677_, lean_object* v_x_1678_, uint8_t v_attrKind_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v___x_1683_; 
lean_inc(v_decl_1677_);
v___x_1683_ = l_Lean_ensureAttrDeclIsMeta(v___x_1676_, v_decl_1677_, v_attrKind_1679_, v___y_1680_, v___y_1681_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v___x_1684_; 
lean_dec_ref_known(v___x_1683_, 1);
v___x_1684_ = l_Lean_Server_registerRpcProcedure(v_decl_1677_, v___y_1680_, v___y_1681_);
return v___x_1684_;
}
else
{
lean_dec(v_decl_1677_);
return v___x_1683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed(lean_object* v___x_1685_, lean_object* v_decl_1686_, lean_object* v_x_1687_, lean_object* v_attrKind_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
uint8_t v_attrKind_boxed_1692_; lean_object* v_res_1693_; 
v_attrKind_boxed_1692_ = lean_unbox(v_attrKind_1688_);
v_res_1693_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(v___x_1685_, v_decl_1686_, v_x_1687_, v_attrKind_boxed_1692_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v_x_1687_);
return v_res_1693_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_));
v___x_1696_ = l_Lean_stringToMessageData(v___x_1695_);
return v___x_1696_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_));
v___x_1699_ = l_Lean_stringToMessageData(v___x_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(lean_object* v___x_1700_, lean_object* v_decl_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1705_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_);
v___x_1706_ = l_Lean_MessageData_ofName(v___x_1700_);
v___x_1707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1705_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
v___x_1708_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_);
v___x_1709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1707_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
v___x_1710_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__4___redArg(v___x_1709_, v___y_1702_, v___y_1703_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed(lean_object* v___x_1711_, lean_object* v_decl_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(v___x_1711_, v_decl_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v_decl_1712_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__31_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_));
v___x_1797_ = l_Lean_registerBuiltinAttribute(v___x_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed(lean_object* v_a_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_();
return v_res_1799_;
}
}
lean_object* runtime_initialize_Lean_Server_Requests(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Rpc_RequestHandling(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
