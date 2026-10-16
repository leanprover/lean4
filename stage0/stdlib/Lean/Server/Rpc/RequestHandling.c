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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
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
uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Server_registerRpcProcedure___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 16, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_registerRpcProcedure___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_registerRpcProcedure___closed__4_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_registerRpcProcedure___closed__5 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___closed__5_value;
static const lean_ctor_object l_Lean_Server_registerRpcProcedure___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_string_object l_Lean_Server_registerRpcProcedure___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Failed to register RPC call handler for '"};
static const lean_object* l_Lean_Server_registerRpcProcedure___closed__18 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___closed__18_value;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__19;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__20;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__21;
static const lean_string_object l_Lean_Server_registerRpcProcedure___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = ": already registered (builtin)"};
static const lean_object* l_Lean_Server_registerRpcProcedure___closed__22 = (const lean_object*)&l_Lean_Server_registerRpcProcedure___closed__22_value;
static lean_once_cell_t l_Lean_Server_registerRpcProcedure___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__23;
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
LEAN_EXPORT uint8_t l_Lean_Server_handleRpcCall___lam__1(lean_object* v___x_293_, lean_object* v___x_294_, lean_object* v_method_295_, lean_object* v_s_296_){
_start:
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_296_);
v___x_298_ = lean_nat_dec_le(v___x_293_, v___x_297_);
lean_dec(v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; lean_object* v_toEnvExtension_300_; lean_object* v_asyncMode_301_; lean_object* v___x_302_; uint8_t v___x_303_; lean_object* v___x_304_; 
v___x_299_ = l_Lean_Server_userRpcProcedures;
v_toEnvExtension_300_ = lean_ctor_get(v___x_299_, 0);
v_asyncMode_301_ = lean_ctor_get(v_toEnvExtension_300_, 2);
v___x_302_ = l_Lean_Server_Snapshots_Snapshot_env(v_s_296_);
v___x_303_ = 0;
v___x_304_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_294_, v___x_299_, v___x_302_, v_method_295_, v_asyncMode_301_, v___x_303_);
if (lean_obj_tag(v___x_304_) == 0)
{
return v___x_298_;
}
else
{
uint8_t v___x_305_; 
lean_dec_ref_known(v___x_304_, 1);
v___x_305_ = 1;
return v___x_305_;
}
}
else
{
lean_dec(v_method_295_);
lean_dec(v___x_294_);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__1___boxed(lean_object* v___x_306_, lean_object* v___x_307_, lean_object* v_method_308_, lean_object* v_s_309_){
_start:
{
uint8_t v_res_310_; lean_object* v_r_311_; 
v_res_310_ = l_Lean_Server_handleRpcCall___lam__1(v___x_306_, v___x_307_, v_method_308_, v_s_309_);
lean_dec_ref(v_s_309_);
lean_dec(v___x_306_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__2(lean_object* v___x_312_, lean_object* v___y_313_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_312_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__2___boxed(lean_object* v___x_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Server_handleRpcCall___lam__2(v___x_316_, v___y_317_);
lean_dec_ref(v___y_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__3(lean_object* v___x_322_, lean_object* v_method_323_, lean_object* v___x_324_, uint8_t v___x_325_, uint64_t v_sessionId_326_, lean_object* v_params_327_, lean_object* v___x_328_, lean_object* v_snap_329_, lean_object* v___y_330_){
_start:
{
lean_object* v___x_332_; lean_object* v_toEnvExtension_333_; lean_object* v_asyncMode_334_; lean_object* v___x_335_; uint8_t v___x_336_; lean_object* v___x_337_; 
v___x_332_ = l_Lean_Server_userRpcProcedures;
v_toEnvExtension_333_ = lean_ctor_get(v___x_332_, 0);
v_asyncMode_334_ = lean_ctor_get(v_toEnvExtension_333_, 2);
v___x_335_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_329_);
v___x_336_ = 0;
lean_inc_ref(v___x_335_);
v___x_337_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_322_, v___x_332_, v___x_335_, v_method_323_, v_asyncMode_334_, v___x_336_);
if (lean_obj_tag(v___x_337_) == 1)
{
lean_object* v_cmdState_338_; lean_object* v_val_339_; lean_object* v_scopes_340_; lean_object* v___x_341_; lean_object* v_opts_342_; lean_object* v___x_343_; 
lean_dec_ref(v___x_328_);
v_cmdState_338_ = lean_ctor_get(v_snap_329_, 2);
v_val_339_ = lean_ctor_get(v___x_337_, 0);
lean_inc_n(v_val_339_, 2);
lean_dec_ref_known(v___x_337_, 1);
v_scopes_340_ = lean_ctor_get(v_cmdState_338_, 2);
v___x_341_ = l_List_head_x21___redArg(v___x_324_, v_scopes_340_);
v_opts_342_ = lean_ctor_get(v___x_341_, 1);
lean_inc_ref(v_opts_342_);
lean_dec(v___x_341_);
v___x_343_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(v___x_335_, v_opts_342_, v_val_339_);
lean_dec_ref(v_opts_342_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_359_; 
lean_dec(v_params_327_);
v_a_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_359_ == 0)
{
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_359_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_359_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
uint8_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_348_ = 4;
v___x_349_ = ((lean_object*)(l_Lean_Server_handleRpcCall___lam__3___closed__0));
v___x_350_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_339_, v___x_325_);
v___x_351_ = lean_string_append(v___x_349_, v___x_350_);
lean_dec_ref(v___x_350_);
v___x_352_ = ((lean_object*)(l_Lean_Server_handleRpcCall___lam__3___closed__1));
v___x_353_ = lean_string_append(v___x_351_, v___x_352_);
v___x_354_ = lean_string_append(v___x_353_, v_a_344_);
lean_dec(v_a_344_);
v___x_355_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*1, v___x_348_);
if (v_isShared_347_ == 0)
{
lean_ctor_set_tag(v___x_346_, 1);
lean_ctor_set(v___x_346_, 0, v___x_355_);
v___x_357_ = v___x_346_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
lean_dec(v_val_339_);
v_a_360_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_a_360_);
lean_dec_ref_known(v___x_343_, 1);
v___x_361_ = lean_box_uint64(v_sessionId_326_);
lean_inc_ref(v___y_330_);
v___x_362_ = lean_apply_4(v_a_360_, v___x_361_, v_params_327_, v___y_330_, lean_box(0));
return v___x_362_;
}
}
else
{
lean_object* v___x_363_; 
lean_dec(v___x_337_);
lean_dec_ref(v___x_335_);
lean_dec(v_params_327_);
v___x_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_328_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__3___boxed(lean_object* v___x_364_, lean_object* v_method_365_, lean_object* v___x_366_, lean_object* v___x_367_, lean_object* v_sessionId_368_, lean_object* v_params_369_, lean_object* v___x_370_, lean_object* v_snap_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
uint8_t v___x_2322__boxed_374_; uint64_t v_sessionId_boxed_375_; lean_object* v_res_376_; 
v___x_2322__boxed_374_ = lean_unbox(v___x_367_);
v_sessionId_boxed_375_ = lean_unbox_uint64(v_sessionId_368_);
lean_dec_ref(v_sessionId_368_);
v_res_376_ = l_Lean_Server_handleRpcCall___lam__3(v___x_364_, v_method_365_, v___x_366_, v___x_2322__boxed_374_, v_sessionId_boxed_375_, v_params_369_, v___x_370_, v_snap_371_, v___y_372_);
lean_dec_ref(v___y_372_);
lean_dec_ref(v_snap_371_);
lean_dec_ref(v___x_366_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_377_, lean_object* v_vals_378_, lean_object* v_i_379_, lean_object* v_k_380_){
_start:
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = lean_array_get_size(v_keys_377_);
v___x_382_ = lean_nat_dec_lt(v_i_379_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
lean_dec(v_i_379_);
v___x_383_ = lean_box(0);
return v___x_383_;
}
else
{
lean_object* v_k_x27_384_; uint8_t v___x_385_; 
v_k_x27_384_ = lean_array_fget_borrowed(v_keys_377_, v_i_379_);
v___x_385_ = lean_name_eq(v_k_380_, v_k_x27_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_nat_add(v_i_379_, v___x_386_);
lean_dec(v_i_379_);
v_i_379_ = v___x_387_;
goto _start;
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_array_fget_borrowed(v_vals_378_, v_i_379_);
lean_dec(v_i_379_);
lean_inc(v___x_389_);
v___x_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_391_, lean_object* v_vals_392_, lean_object* v_i_393_, lean_object* v_k_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(v_keys_391_, v_vals_392_, v_i_393_, v_k_394_);
lean_dec(v_k_394_);
lean_dec_ref(v_vals_392_);
lean_dec_ref(v_keys_391_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(lean_object* v_x_396_, size_t v_x_397_, lean_object* v_x_398_){
_start:
{
if (lean_obj_tag(v_x_396_) == 0)
{
lean_object* v_es_399_; lean_object* v___x_400_; size_t v___x_401_; size_t v___x_402_; lean_object* v_j_403_; lean_object* v___x_404_; 
v_es_399_ = lean_ctor_get(v_x_396_, 0);
v___x_400_ = lean_box(2);
v___x_401_ = ((size_t)31ULL);
v___x_402_ = lean_usize_land(v_x_397_, v___x_401_);
v_j_403_ = lean_usize_to_nat(v___x_402_);
v___x_404_ = lean_array_get_borrowed(v___x_400_, v_es_399_, v_j_403_);
lean_dec(v_j_403_);
switch(lean_obj_tag(v___x_404_))
{
case 0:
{
lean_object* v_key_405_; lean_object* v_val_406_; uint8_t v___x_407_; 
v_key_405_ = lean_ctor_get(v___x_404_, 0);
v_val_406_ = lean_ctor_get(v___x_404_, 1);
v___x_407_ = lean_name_eq(v_x_398_, v_key_405_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
v___x_408_ = lean_box(0);
return v___x_408_;
}
else
{
lean_object* v___x_409_; 
lean_inc(v_val_406_);
v___x_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_409_, 0, v_val_406_);
return v___x_409_;
}
}
case 1:
{
lean_object* v_node_410_; size_t v___x_411_; size_t v___x_412_; 
v_node_410_ = lean_ctor_get(v___x_404_, 0);
v___x_411_ = ((size_t)5ULL);
v___x_412_ = lean_usize_shift_right(v_x_397_, v___x_411_);
v_x_396_ = v_node_410_;
v_x_397_ = v___x_412_;
goto _start;
}
default: 
{
lean_object* v___x_414_; 
v___x_414_ = lean_box(0);
return v___x_414_;
}
}
}
else
{
lean_object* v_ks_415_; lean_object* v_vs_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_ks_415_ = lean_ctor_get(v_x_396_, 0);
v_vs_416_ = lean_ctor_get(v_x_396_, 1);
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(v_ks_415_, v_vs_416_, v___x_417_, v_x_398_);
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg___boxed(lean_object* v_x_419_, lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
size_t v_x_2413__boxed_422_; lean_object* v_res_423_; 
v_x_2413__boxed_422_ = lean_unbox_usize(v_x_420_);
lean_dec(v_x_420_);
v_res_423_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(v_x_419_, v_x_2413__boxed_422_, v_x_421_);
lean_dec(v_x_421_);
lean_dec_ref(v_x_419_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
uint64_t v___y_427_; 
if (lean_obj_tag(v_x_425_) == 0)
{
uint64_t v___x_430_; 
v___x_430_ = 1723ULL;
v___y_427_ = v___x_430_;
goto v___jp_426_;
}
else
{
uint64_t v_hash_431_; 
v_hash_431_ = lean_ctor_get_uint64(v_x_425_, sizeof(void*)*2);
v___y_427_ = v_hash_431_;
goto v___jp_426_;
}
v___jp_426_:
{
size_t v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_uint64_to_usize(v___y_427_);
v___x_429_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(v_x_424_, v___x_428_, v_x_425_);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg___boxed(lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(v_x_432_, v_x_433_);
lean_dec(v_x_433_);
lean_dec_ref(v_x_432_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall(lean_object* v_p_437_, lean_object* v_a_438_){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v_toTextDocumentPositionParams_444_; uint64_t v_sessionId_445_; lean_object* v_method_446_; lean_object* v_params_447_; lean_object* v___x_448_; 
v___x_440_ = lean_box(0);
v___x_441_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_442_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_443_ = lean_st_ref_get(v___x_442_);
v_toTextDocumentPositionParams_444_ = lean_ctor_get(v_p_437_, 0);
lean_inc_ref(v_toTextDocumentPositionParams_444_);
v_sessionId_445_ = lean_ctor_get_uint64(v_p_437_, sizeof(void*)*3);
v_method_446_ = lean_ctor_get(v_p_437_, 1);
lean_inc(v_method_446_);
v_params_447_ = lean_ctor_get(v_p_437_, 2);
lean_inc(v_params_447_);
lean_dec_ref(v_p_437_);
v___x_448_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(v___x_443_, v_method_446_);
lean_dec(v___x_443_);
if (lean_obj_tag(v___x_448_) == 1)
{
lean_object* v_val_449_; lean_object* v___x_450_; lean_object* v___f_451_; lean_object* v___x_452_; 
lean_dec(v_method_446_);
lean_dec_ref(v_toTextDocumentPositionParams_444_);
v_val_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_val_449_);
lean_dec_ref_known(v___x_448_, 1);
v___x_450_ = lean_box_uint64(v_sessionId_445_);
v___f_451_ = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__0___boxed), 5, 3);
lean_closure_set(v___f_451_, 0, v_val_449_);
lean_closure_set(v___f_451_, 1, v___x_450_);
lean_closure_set(v___f_451_, 2, v_params_447_);
v___x_452_ = l_Lean_Server_RequestM_asTask___redArg(v___f_451_, v_a_438_);
return v___x_452_;
}
else
{
lean_object* v___x_453_; lean_object* v_a_454_; lean_object* v_toEditableDocumentCore_455_; lean_object* v_meta_456_; lean_object* v_text_457_; lean_object* v_position_458_; lean_object* v___x_459_; lean_object* v___f_460_; uint8_t v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___f_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___f_472_; lean_object* v___x_473_; 
lean_dec(v___x_448_);
v___x_453_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1(v_a_438_);
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
lean_dec_ref(v___x_453_);
v_toEditableDocumentCore_455_ = lean_ctor_get(v_a_454_, 0);
v_meta_456_ = lean_ctor_get(v_toEditableDocumentCore_455_, 0);
v_text_457_ = lean_ctor_get(v_meta_456_, 3);
v_position_458_ = lean_ctor_get(v_toTextDocumentPositionParams_444_, 1);
lean_inc_ref(v_position_458_);
lean_dec_ref(v_toTextDocumentPositionParams_444_);
v___x_459_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_457_, v_position_458_);
lean_inc_n(v_method_446_, 2);
v___f_460_ = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__1___boxed), 4, 3);
lean_closure_set(v___f_460_, 0, v___x_459_);
lean_closure_set(v___f_460_, 1, v___x_440_);
lean_closure_set(v___f_460_, 2, v_method_446_);
v___x_461_ = 2;
v___x_462_ = ((lean_object*)(l_Lean_Server_handleRpcCall___closed__0));
v___x_463_ = 1;
v___x_464_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_446_, v___x_463_);
v___x_465_ = lean_string_append(v___x_462_, v___x_464_);
lean_dec_ref(v___x_464_);
v___x_466_ = ((lean_object*)(l_Lean_Server_handleRpcCall___closed__1));
v___x_467_ = lean_string_append(v___x_465_, v___x_466_);
v___x_468_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set_uint8(v___x_468_, sizeof(void*)*1, v___x_461_);
lean_inc_ref(v___x_468_);
v___f_469_ = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__2___boxed), 3, 1);
lean_closure_set(v___f_469_, 0, v___x_468_);
v___x_470_ = lean_box(v___x_463_);
v___x_471_ = lean_box_uint64(v_sessionId_445_);
v___f_472_ = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__3___boxed), 10, 7);
lean_closure_set(v___f_472_, 0, v___x_440_);
lean_closure_set(v___f_472_, 1, v_method_446_);
lean_closure_set(v___f_472_, 2, v___x_441_);
lean_closure_set(v___f_472_, 3, v___x_470_);
lean_closure_set(v___f_472_, 4, v___x_471_);
lean_closure_set(v___f_472_, 5, v_params_447_);
lean_closure_set(v___f_472_, 6, v___x_468_);
v___x_473_ = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(v_a_454_, v___f_460_, v___f_469_, v___f_472_, v_a_438_);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___boxed(lean_object* v_p_474_, lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_Server_handleRpcCall(v_p_474_, v_a_475_);
lean_dec_ref(v_a_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0(lean_object* v_00_u03b2_478_, lean_object* v_x_479_, lean_object* v_x_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(v_x_479_, v_x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___boxed(lean_object* v_00_u03b2_482_, lean_object* v_x_483_, lean_object* v_x_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0(v_00_u03b2_482_, v_x_483_, v_x_484_);
lean_dec(v_x_484_);
lean_dec_ref(v_x_483_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0(lean_object* v_00_u03b2_486_, lean_object* v_x_487_, size_t v_x_488_, lean_object* v_x_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(v_x_487_, v_x_488_, v_x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___boxed(lean_object* v_00_u03b2_491_, lean_object* v_x_492_, lean_object* v_x_493_, lean_object* v_x_494_){
_start:
{
size_t v_x_2546__boxed_495_; lean_object* v_res_496_; 
v_x_2546__boxed_495_ = lean_unbox_usize(v_x_493_);
lean_dec(v_x_493_);
v_res_496_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0(v_00_u03b2_491_, v_x_492_, v_x_2546__boxed_495_, v_x_494_);
lean_dec(v_x_494_);
lean_dec_ref(v_x_492_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_497_, lean_object* v_keys_498_, lean_object* v_vals_499_, lean_object* v_heq_500_, lean_object* v_i_501_, lean_object* v_k_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(v_keys_498_, v_vals_499_, v_i_501_, v_k_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_504_, lean_object* v_keys_505_, lean_object* v_vals_506_, lean_object* v_heq_507_, lean_object* v_i_508_, lean_object* v_k_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2(v_00_u03b2_504_, v_keys_505_, v_vals_506_, v_heq_507_, v_i_508_, v_k_509_);
lean_dec(v_k_509_);
lean_dec_ref(v_vals_506_);
lean_dec_ref(v_keys_505_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_511_, uint8_t v_val_512_, lean_object* v___y_513_){
_start:
{
if (lean_obj_tag(v___y_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
lean_dec(v_serialize_x3f_511_);
v_a_514_ = lean_ctor_get(v___y_513_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___y_513_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___y_513_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___y_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
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
if (lean_obj_tag(v_serialize_x3f_511_) == 1)
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_533_; 
v_a_522_ = lean_ctor_get(v___y_513_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___y_513_);
if (v_isSharedCheck_533_ == 0)
{
v___x_524_ = v___y_513_;
v_isShared_525_ = v_isSharedCheck_533_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___y_513_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_533_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v_val_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v_val_526_ = lean_ctor_get(v_serialize_x3f_511_, 0);
lean_inc(v_val_526_);
lean_dec_ref_known(v_serialize_x3f_511_, 1);
v___x_527_ = lean_box(0);
v___x_528_ = lean_apply_1(v_val_526_, v_a_522_);
v___x_529_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*2, v_val_512_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_529_);
v___x_531_ = v___x_524_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_544_; 
lean_dec(v_serialize_x3f_511_);
v_a_534_ = lean_ctor_get(v___y_513_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___y_513_);
if (v_isSharedCheck_544_ == 0)
{
v___x_536_ = v___y_513_;
v_isShared_537_ = v_isSharedCheck_544_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___y_513_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_544_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
lean_inc(v_a_534_);
v___x_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_538_, 0, v_a_534_);
v___x_539_ = l_Lean_Json_compress(v_a_534_);
v___x_540_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*2, v_val_512_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_540_);
v___x_542_ = v___x_536_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_545_, lean_object* v_val_546_, lean_object* v___y_547_){
_start:
{
uint8_t v_val_789__boxed_548_; lean_object* v_res_549_; 
v_val_789__boxed_548_ = lean_unbox(v_val_546_);
v_res_549_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_545_, v_val_789__boxed_548_, v___y_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8___redArg(lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
lean_object* v_ks_554_; lean_object* v_vs_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_579_; 
v_ks_554_ = lean_ctor_get(v_x_550_, 0);
v_vs_555_ = lean_ctor_get(v_x_550_, 1);
v_isSharedCheck_579_ = !lean_is_exclusive(v_x_550_);
if (v_isSharedCheck_579_ == 0)
{
v___x_557_ = v_x_550_;
v_isShared_558_ = v_isSharedCheck_579_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_vs_555_);
lean_inc(v_ks_554_);
lean_dec(v_x_550_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_579_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_559_ = lean_array_get_size(v_ks_554_);
v___x_560_ = lean_nat_dec_lt(v_x_551_, v___x_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
lean_dec(v_x_551_);
v___x_561_ = lean_array_push(v_ks_554_, v_x_552_);
v___x_562_ = lean_array_push(v_vs_555_, v_x_553_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v___x_562_);
lean_ctor_set(v___x_557_, 0, v___x_561_);
v___x_564_ = v___x_557_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
else
{
lean_object* v_k_x27_566_; uint8_t v___x_567_; 
v_k_x27_566_ = lean_array_fget_borrowed(v_ks_554_, v_x_551_);
v___x_567_ = lean_string_dec_eq(v_x_552_, v_k_x27_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_569_; 
if (v_isShared_558_ == 0)
{
v___x_569_ = v___x_557_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_ks_554_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_vs_555_);
v___x_569_ = v_reuseFailAlloc_573_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_unsigned_to_nat(1u);
v___x_571_ = lean_nat_add(v_x_551_, v___x_570_);
lean_dec(v_x_551_);
v_x_550_ = v___x_569_;
v_x_551_ = v___x_571_;
goto _start;
}
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_574_ = lean_array_fset(v_ks_554_, v_x_551_, v_x_552_);
v___x_575_ = lean_array_fset(v_vs_555_, v_x_551_, v_x_553_);
lean_dec(v_x_551_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v___x_575_);
lean_ctor_set(v___x_557_, 0, v___x_574_);
v___x_577_ = v___x_557_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7___redArg(lean_object* v_n_580_, lean_object* v_k_581_, lean_object* v_v_582_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_unsigned_to_nat(0u);
v___x_584_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8___redArg(v_n_580_, v___x_583_, v_k_581_, v_v_582_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* v_x_586_, size_t v_x_587_, size_t v_x_588_, lean_object* v_x_589_, lean_object* v_x_590_){
_start:
{
if (lean_obj_tag(v_x_586_) == 0)
{
lean_object* v_es_591_; size_t v___x_592_; size_t v___x_593_; lean_object* v_j_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v_es_591_ = lean_ctor_get(v_x_586_, 0);
v___x_592_ = ((size_t)31ULL);
v___x_593_ = lean_usize_land(v_x_587_, v___x_592_);
v_j_594_ = lean_usize_to_nat(v___x_593_);
v___x_595_ = lean_array_get_size(v_es_591_);
v___x_596_ = lean_nat_dec_lt(v_j_594_, v___x_595_);
if (v___x_596_ == 0)
{
lean_dec(v_j_594_);
lean_dec(v_x_590_);
lean_dec_ref(v_x_589_);
return v_x_586_;
}
else
{
lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_635_; 
lean_inc_ref(v_es_591_);
v_isSharedCheck_635_ = !lean_is_exclusive(v_x_586_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; 
v_unused_636_ = lean_ctor_get(v_x_586_, 0);
lean_dec(v_unused_636_);
v___x_598_ = v_x_586_;
v_isShared_599_ = v_isSharedCheck_635_;
goto v_resetjp_597_;
}
else
{
lean_dec(v_x_586_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_635_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v_v_600_; lean_object* v___x_601_; lean_object* v_xs_x27_602_; lean_object* v___y_604_; 
v_v_600_ = lean_array_fget(v_es_591_, v_j_594_);
v___x_601_ = lean_box(0);
v_xs_x27_602_ = lean_array_fset(v_es_591_, v_j_594_, v___x_601_);
switch(lean_obj_tag(v_v_600_))
{
case 0:
{
lean_object* v_key_609_; lean_object* v_val_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_620_; 
v_key_609_ = lean_ctor_get(v_v_600_, 0);
v_val_610_ = lean_ctor_get(v_v_600_, 1);
v_isSharedCheck_620_ = !lean_is_exclusive(v_v_600_);
if (v_isSharedCheck_620_ == 0)
{
v___x_612_ = v_v_600_;
v_isShared_613_ = v_isSharedCheck_620_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_val_610_);
lean_inc(v_key_609_);
lean_dec(v_v_600_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_620_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
uint8_t v___x_614_; 
v___x_614_ = lean_string_dec_eq(v_x_589_, v_key_609_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; 
lean_del_object(v___x_612_);
v___x_615_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_609_, v_val_610_, v_x_589_, v_x_590_);
v___x_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
v___y_604_ = v___x_616_;
goto v___jp_603_;
}
else
{
lean_object* v___x_618_; 
lean_dec(v_val_610_);
lean_dec(v_key_609_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 1, v_x_590_);
lean_ctor_set(v___x_612_, 0, v_x_589_);
v___x_618_ = v___x_612_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_x_589_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_x_590_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
v___y_604_ = v___x_618_;
goto v___jp_603_;
}
}
}
}
case 1:
{
lean_object* v_node_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_633_; 
v_node_621_ = lean_ctor_get(v_v_600_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v_v_600_);
if (v_isSharedCheck_633_ == 0)
{
v___x_623_ = v_v_600_;
v_isShared_624_ = v_isSharedCheck_633_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_node_621_);
lean_dec(v_v_600_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_633_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
size_t v___x_625_; size_t v___x_626_; size_t v___x_627_; size_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_625_ = ((size_t)5ULL);
v___x_626_ = lean_usize_shift_right(v_x_587_, v___x_625_);
v___x_627_ = ((size_t)1ULL);
v___x_628_ = lean_usize_add(v_x_588_, v___x_627_);
v___x_629_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_node_621_, v___x_626_, v___x_628_, v_x_589_, v_x_590_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v___x_629_);
v___x_631_ = v___x_623_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
v___y_604_ = v___x_631_;
goto v___jp_603_;
}
}
}
default: 
{
lean_object* v___x_634_; 
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v_x_589_);
lean_ctor_set(v___x_634_, 1, v_x_590_);
v___y_604_ = v___x_634_;
goto v___jp_603_;
}
}
v___jp_603_:
{
lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_605_ = lean_array_fset(v_xs_x27_602_, v_j_594_, v___y_604_);
lean_dec(v_j_594_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_605_);
v___x_607_ = v___x_598_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
else
{
lean_object* v_ks_637_; lean_object* v_vs_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_656_; 
v_ks_637_ = lean_ctor_get(v_x_586_, 0);
v_vs_638_ = lean_ctor_get(v_x_586_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_x_586_);
if (v_isSharedCheck_656_ == 0)
{
v___x_640_ = v_x_586_;
v_isShared_641_ = v_isSharedCheck_656_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_vs_638_);
lean_inc(v_ks_637_);
lean_dec(v_x_586_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_656_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_ks_637_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_vs_638_);
v___x_643_ = v_reuseFailAlloc_655_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v_newNode_644_; size_t v___x_645_; uint8_t v___x_646_; 
v_newNode_644_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7___redArg(v___x_643_, v_x_589_, v_x_590_);
v___x_645_ = ((size_t)7ULL);
v___x_646_ = lean_usize_dec_le(v___x_645_, v_x_588_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_647_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_644_);
v___x_648_ = lean_unsigned_to_nat(4u);
v___x_649_ = lean_nat_dec_lt(v___x_647_, v___x_648_);
lean_dec(v___x_647_);
if (v___x_649_ == 0)
{
lean_object* v_ks_650_; lean_object* v_vs_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_ks_650_ = lean_ctor_get(v_newNode_644_, 0);
lean_inc_ref(v_ks_650_);
v_vs_651_ = lean_ctor_get(v_newNode_644_, 1);
lean_inc_ref(v_vs_651_);
lean_dec_ref(v_newNode_644_);
v___x_652_ = lean_unsigned_to_nat(0u);
v___x_653_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
v___x_654_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_x_588_, v_ks_650_, v_vs_651_, v___x_652_, v___x_653_);
lean_dec_ref(v_vs_651_);
lean_dec_ref(v_ks_650_);
return v___x_654_;
}
else
{
return v_newNode_644_;
}
}
else
{
return v_newNode_644_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(size_t v_depth_657_, lean_object* v_keys_658_, lean_object* v_vals_659_, lean_object* v_i_660_, lean_object* v_entries_661_){
_start:
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = lean_array_get_size(v_keys_658_);
v___x_663_ = lean_nat_dec_lt(v_i_660_, v___x_662_);
if (v___x_663_ == 0)
{
lean_dec(v_i_660_);
return v_entries_661_;
}
else
{
lean_object* v_k_664_; lean_object* v_v_665_; uint64_t v___x_666_; size_t v_h_667_; size_t v___x_668_; lean_object* v___x_669_; size_t v___x_670_; size_t v___x_671_; size_t v___x_672_; size_t v_h_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_k_664_ = lean_array_fget_borrowed(v_keys_658_, v_i_660_);
v_v_665_ = lean_array_fget_borrowed(v_vals_659_, v_i_660_);
v___x_666_ = lean_string_hash(v_k_664_);
v_h_667_ = lean_uint64_to_usize(v___x_666_);
v___x_668_ = ((size_t)5ULL);
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = ((size_t)1ULL);
v___x_671_ = lean_usize_sub(v_depth_657_, v___x_670_);
v___x_672_ = lean_usize_mul(v___x_668_, v___x_671_);
v_h_673_ = lean_usize_shift_right(v_h_667_, v___x_672_);
v___x_674_ = lean_nat_add(v_i_660_, v___x_669_);
lean_dec(v_i_660_);
lean_inc(v_v_665_);
lean_inc(v_k_664_);
v___x_675_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_entries_661_, v_h_673_, v_depth_657_, v_k_664_, v_v_665_);
v_i_660_ = v___x_674_;
v_entries_661_ = v___x_675_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_depth_677_, lean_object* v_keys_678_, lean_object* v_vals_679_, lean_object* v_i_680_, lean_object* v_entries_681_){
_start:
{
size_t v_depth_boxed_682_; lean_object* v_res_683_; 
v_depth_boxed_682_ = lean_unbox_usize(v_depth_677_);
lean_dec(v_depth_677_);
v_res_683_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_depth_boxed_682_, v_keys_678_, v_vals_679_, v_i_680_, v_entries_681_);
lean_dec_ref(v_vals_679_);
lean_dec_ref(v_keys_678_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_x_684_, lean_object* v_x_685_, lean_object* v_x_686_, lean_object* v_x_687_, lean_object* v_x_688_){
_start:
{
size_t v_x_934__boxed_689_; size_t v_x_935__boxed_690_; lean_object* v_res_691_; 
v_x_934__boxed_689_ = lean_unbox_usize(v_x_685_);
lean_dec(v_x_685_);
v_x_935__boxed_690_ = lean_unbox_usize(v_x_686_);
lean_dec(v_x_686_);
v_res_691_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_684_, v_x_934__boxed_689_, v_x_935__boxed_690_, v_x_687_, v_x_688_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_){
_start:
{
uint64_t v___x_695_; size_t v___x_696_; size_t v___x_697_; lean_object* v___x_698_; 
v___x_695_ = lean_string_hash(v_x_693_);
v___x_696_ = lean_uint64_to_usize(v___x_695_);
v___x_697_ = ((size_t)1ULL);
v___x_698_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_692_, v___x_696_, v___x_697_, v_x_693_, v_x_694_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_701_){
_start:
{
lean_object* v___x_702_; 
lean_inc(v_params_701_);
v___x_702_ = l_Lean_Lsp_instFromJsonRpcCallParams_fromJson(v_params_701_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_718_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_718_ == 0)
{
v___x_705_ = v___x_702_;
v_isShared_706_ = v_isSharedCheck_718_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_718_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
uint8_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_707_ = 3;
v___x_708_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_709_ = l_Lean_Json_compress(v_params_701_);
v___x_710_ = lean_string_append(v___x_708_, v___x_709_);
lean_dec_ref(v___x_709_);
v___x_711_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__1));
v___x_712_ = lean_string_append(v___x_710_, v___x_711_);
v___x_713_ = lean_string_append(v___x_712_, v_a_703_);
lean_dec(v_a_703_);
v___x_714_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set_uint8(v___x_714_, sizeof(void*)*1, v___x_707_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_714_);
v___x_716_ = v___x_705_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v_params_701_);
v_a_719_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_702_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_702_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_727_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0(v_params_727_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_729_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_729_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
lean_ctor_set_tag(v___x_732_, 1);
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
v_a_738_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_729_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_729_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set_tag(v___x_740_, 0);
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_746_, lean_object* v_a_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_746_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_749_, lean_object* v___f_750_, lean_object* v_j_751_, lean_object* v___y_752_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_751_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_756_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
lean_dec_ref_known(v___x_754_, 1);
lean_inc_ref(v___y_752_);
v___x_756_ = lean_apply_3(v_handler_749_, v_a_755_, v___y_752_, lean_box(0));
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_765_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_765_ == 0)
{
v___x_759_ = v___x_756_;
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_756_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_761_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_750_, v_a_757_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_761_);
v___x_763_ = v___x_759_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec_ref(v___f_750_);
v_a_766_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_756_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_756_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec_ref(v___f_750_);
lean_dec_ref(v_handler_749_);
v_a_774_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_754_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_754_);
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
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_782_, lean_object* v___f_783_, lean_object* v_j_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2(v_handler_782_, v___f_783_, v_j_784_, v___y_785_);
lean_dec_ref(v___y_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0(v_j_788_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_807_; 
v_a_798_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_807_ == 0)
{
v___x_800_ = v___x_789_;
v_isShared_801_ = v_isSharedCheck_807_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_789_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_807_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v_toTextDocumentPositionParams_802_; lean_object* v_textDocument_803_; lean_object* v___x_805_; 
v_toTextDocumentPositionParams_802_ = lean_ctor_get(v_a_798_, 0);
lean_inc_ref(v_toTextDocumentPositionParams_802_);
lean_dec(v_a_798_);
v_textDocument_803_ = lean_ctor_get(v_toTextDocumentPositionParams_802_, 0);
lean_inc_ref(v_textDocument_803_);
lean_dec_ref(v_toTextDocumentPositionParams_802_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v_textDocument_803_);
v___x_805_ = v___x_800_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_textDocument_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_keys_808_, lean_object* v_i_809_, lean_object* v_k_810_){
_start:
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = lean_array_get_size(v_keys_808_);
v___x_812_ = lean_nat_dec_lt(v_i_809_, v___x_811_);
if (v___x_812_ == 0)
{
lean_dec(v_i_809_);
return v___x_812_;
}
else
{
lean_object* v_k_x27_813_; uint8_t v___x_814_; 
v_k_x27_813_ = lean_array_fget_borrowed(v_keys_808_, v_i_809_);
v___x_814_ = lean_string_dec_eq(v_k_810_, v_k_x27_813_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_unsigned_to_nat(1u);
v___x_816_ = lean_nat_add(v_i_809_, v___x_815_);
lean_dec(v_i_809_);
v_i_809_ = v___x_816_;
goto _start;
}
else
{
lean_dec(v_i_809_);
return v___x_812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_keys_818_, lean_object* v_i_819_, lean_object* v_k_820_){
_start:
{
uint8_t v_res_821_; lean_object* v_r_822_; 
v_res_821_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(v_keys_818_, v_i_819_, v_k_820_);
lean_dec_ref(v_k_820_);
lean_dec_ref(v_keys_818_);
v_r_822_ = lean_box(v_res_821_);
return v_r_822_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object* v_x_823_, size_t v_x_824_, lean_object* v_x_825_){
_start:
{
if (lean_obj_tag(v_x_823_) == 0)
{
lean_object* v_es_826_; lean_object* v___x_827_; size_t v___x_828_; size_t v___x_829_; lean_object* v_j_830_; lean_object* v___x_831_; 
v_es_826_ = lean_ctor_get(v_x_823_, 0);
v___x_827_ = lean_box(2);
v___x_828_ = ((size_t)31ULL);
v___x_829_ = lean_usize_land(v_x_824_, v___x_828_);
v_j_830_ = lean_usize_to_nat(v___x_829_);
v___x_831_ = lean_array_get_borrowed(v___x_827_, v_es_826_, v_j_830_);
lean_dec(v_j_830_);
switch(lean_obj_tag(v___x_831_))
{
case 0:
{
lean_object* v_key_832_; uint8_t v___x_833_; 
v_key_832_ = lean_ctor_get(v___x_831_, 0);
v___x_833_ = lean_string_dec_eq(v_x_825_, v_key_832_);
return v___x_833_;
}
case 1:
{
lean_object* v_node_834_; size_t v___x_835_; size_t v___x_836_; 
v_node_834_ = lean_ctor_get(v___x_831_, 0);
v___x_835_ = ((size_t)5ULL);
v___x_836_ = lean_usize_shift_right(v_x_824_, v___x_835_);
v_x_823_ = v_node_834_;
v_x_824_ = v___x_836_;
goto _start;
}
default: 
{
uint8_t v___x_838_; 
v___x_838_ = 0;
return v___x_838_;
}
}
}
else
{
lean_object* v_ks_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v_ks_839_ = lean_ctor_get(v_x_823_, 0);
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(v_ks_839_, v___x_840_, v_x_825_);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_x_844_){
_start:
{
size_t v_x_1304__boxed_845_; uint8_t v_res_846_; lean_object* v_r_847_; 
v_x_1304__boxed_845_ = lean_unbox_usize(v_x_843_);
lean_dec(v_x_843_);
v_res_846_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_842_, v_x_1304__boxed_845_, v_x_844_);
lean_dec_ref(v_x_844_);
lean_dec_ref(v_x_842_);
v_r_847_ = lean_box(v_res_846_);
return v_r_847_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
uint64_t v___x_850_; size_t v___x_851_; uint8_t v___x_852_; 
v___x_850_ = lean_string_hash(v_x_849_);
v___x_851_ = lean_uint64_to_usize(v___x_850_);
v___x_852_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_848_, v___x_851_, v_x_849_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_x_853_, lean_object* v_x_854_){
_start:
{
uint8_t v_res_855_; lean_object* v_r_856_; 
v_res_855_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_853_, v_x_854_);
lean_dec_ref(v_x_854_);
lean_dec_ref(v_x_853_);
v_r_856_ = lean_box(v_res_855_);
return v_r_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0(lean_object* v_method_861_, lean_object* v_handler_862_, lean_object* v_serialize_x3f_863_){
_start:
{
lean_object* v___f_865_; uint8_t v___x_866_; 
v___f_865_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__0));
v___x_866_ = l_Lean_initializing();
if (v___x_866_ == 0)
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec(v_serialize_x3f_863_);
lean_dec_ref(v_handler_862_);
v___x_867_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__1));
v___x_868_ = lean_string_append(v___x_867_, v_method_861_);
lean_dec_ref(v_method_861_);
v___x_869_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__2));
v___x_870_ = lean_string_append(v___x_868_, v___x_869_);
v___x_871_ = lean_mk_io_user_error(v___x_870_);
v___x_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
return v___x_872_;
}
else
{
lean_object* v___x_873_; lean_object* v___f_874_; lean_object* v___f_875_; lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_873_ = lean_box(v___x_866_);
v___f_874_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_874_, 0, v_serialize_x3f_863_);
lean_closure_set(v___f_874_, 1, v___x_873_);
v___f_875_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_875_, 0, v_handler_862_);
lean_closure_set(v___f_875_, 1, v___f_874_);
v___x_876_ = l_Lean_Server_requestHandlers;
v___x_877_ = lean_st_ref_get(v___x_876_);
v___x_878_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_877_, v_method_861_);
lean_dec(v___x_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_879_ = lean_st_ref_take(v___x_876_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v___f_865_);
lean_ctor_set(v___x_880_, 1, v___f_875_);
v___x_881_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_879_, v_method_861_, v___x_880_);
v___x_882_ = lean_st_ref_put(v___x_876_, v___x_881_);
v___x_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
return v___x_883_;
}
else
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
lean_dec_ref(v___f_875_);
v___x_884_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__1));
v___x_885_ = lean_string_append(v___x_884_, v_method_861_);
lean_dec_ref(v_method_861_);
v___x_886_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__3));
v___x_887_ = lean_string_append(v___x_885_, v___x_886_);
v___x_888_ = lean_mk_io_user_error(v___x_887_);
v___x_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_890_, lean_object* v_handler_891_, lean_object* v_serialize_x3f_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0(v_method_890_, v_handler_891_, v_serialize_x3f_892_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_898_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_));
v___x_899_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_));
v___x_900_ = lean_box(0);
v___x_901_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0(v___x_898_, v___x_899_, v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2____boxed(lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_();
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_904_, lean_object* v_a_905_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_904_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1(v_params_908_, v_a_909_);
lean_dec_ref(v_a_909_);
return v_res_911_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_912_, lean_object* v_x_913_, lean_object* v_x_914_){
_start:
{
uint8_t v___x_915_; 
v___x_915_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_913_, v_x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_916_, lean_object* v_x_917_, lean_object* v_x_918_){
_start:
{
uint8_t v_res_919_; lean_object* v_r_920_; 
v_res_919_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_916_, v_x_917_, v_x_918_);
lean_dec_ref(v_x_918_);
lean_dec_ref(v_x_917_);
v_r_920_ = lean_box(v_res_919_);
return v_r_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_00_u03b2_921_, lean_object* v_x_922_, lean_object* v_x_923_, lean_object* v_x_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_922_, v_x_923_, v_x_924_);
return v___x_925_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object* v_00_u03b2_926_, lean_object* v_x_927_, size_t v_x_928_, lean_object* v_x_929_){
_start:
{
uint8_t v___x_930_; 
v___x_930_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_927_, v_x_928_, v_x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_931_, lean_object* v_x_932_, lean_object* v_x_933_, lean_object* v_x_934_){
_start:
{
size_t v_x_1461__boxed_935_; uint8_t v_res_936_; lean_object* v_r_937_; 
v_x_1461__boxed_935_ = lean_unbox_usize(v_x_933_);
lean_dec(v_x_933_);
v_res_936_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_00_u03b2_931_, v_x_932_, v_x_1461__boxed_935_, v_x_934_);
lean_dec_ref(v_x_934_);
lean_dec_ref(v_x_932_);
v_r_937_ = lean_box(v_res_936_);
return v_r_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* v_00_u03b2_938_, lean_object* v_x_939_, size_t v_x_940_, size_t v_x_941_, lean_object* v_x_942_, lean_object* v_x_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_939_, v_x_940_, v_x_941_, v_x_942_, v_x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_945_, lean_object* v_x_946_, lean_object* v_x_947_, lean_object* v_x_948_, lean_object* v_x_949_, lean_object* v_x_950_){
_start:
{
size_t v_x_1472__boxed_951_; size_t v_x_1473__boxed_952_; lean_object* v_res_953_; 
v_x_1472__boxed_951_ = lean_unbox_usize(v_x_947_);
lean_dec(v_x_947_);
v_x_1473__boxed_952_ = lean_unbox_usize(v_x_948_);
lean_dec(v_x_948_);
v_res_953_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_945_, v_x_946_, v_x_1472__boxed_951_, v_x_1473__boxed_952_, v_x_949_, v_x_950_);
return v_res_953_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_954_, lean_object* v_keys_955_, lean_object* v_vals_956_, lean_object* v_heq_957_, lean_object* v_i_958_, lean_object* v_k_959_){
_start:
{
uint8_t v___x_960_; 
v___x_960_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(v_keys_955_, v_i_958_, v_k_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_961_, lean_object* v_keys_962_, lean_object* v_vals_963_, lean_object* v_heq_964_, lean_object* v_i_965_, lean_object* v_k_966_){
_start:
{
uint8_t v_res_967_; lean_object* v_r_968_; 
v_res_967_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4(v_00_u03b2_961_, v_keys_962_, v_vals_963_, v_heq_964_, v_i_965_, v_k_966_);
lean_dec_ref(v_k_966_);
lean_dec_ref(v_vals_963_);
lean_dec_ref(v_keys_962_);
v_r_968_ = lean_box(v_res_967_);
return v_r_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_969_, lean_object* v_n_970_, lean_object* v_k_971_, lean_object* v_v_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7___redArg(v_n_970_, v_k_971_, v_v_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_974_, size_t v_depth_975_, lean_object* v_keys_976_, lean_object* v_vals_977_, lean_object* v_heq_978_, lean_object* v_i_979_, lean_object* v_entries_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_depth_975_, v_keys_976_, v_vals_977_, v_i_979_, v_entries_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_982_, lean_object* v_depth_983_, lean_object* v_keys_984_, lean_object* v_vals_985_, lean_object* v_heq_986_, lean_object* v_i_987_, lean_object* v_entries_988_){
_start:
{
size_t v_depth_boxed_989_; lean_object* v_res_990_; 
v_depth_boxed_989_ = lean_unbox_usize(v_depth_983_);
lean_dec(v_depth_983_);
v_res_990_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(v_00_u03b2_982_, v_depth_boxed_989_, v_keys_984_, v_vals_985_, v_heq_986_, v_i_987_, v_entries_988_);
lean_dec_ref(v_vals_985_);
lean_dec_ref(v_keys_984_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8(lean_object* v_00_u03b2_991_, lean_object* v_x_992_, lean_object* v_x_993_, lean_object* v_x_994_, lean_object* v_x_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8___redArg(v_x_992_, v_x_993_, v_x_994_, v_x_995_);
return v___x_996_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_wrapRpcProcedure___redArg___lam__0(uint64_t v_x_997_, uint64_t v_y_998_){
_start:
{
uint8_t v___x_999_; 
v___x_999_ = lean_uint64_dec_lt(v_x_997_, v_y_998_);
if (v___x_999_ == 0)
{
uint8_t v___x_1000_; 
v___x_1000_ = lean_uint64_dec_eq(v_x_997_, v_y_998_);
if (v___x_1000_ == 0)
{
uint8_t v___x_1001_; 
v___x_1001_ = 2;
return v___x_1001_;
}
else
{
uint8_t v___x_1002_; 
v___x_1002_ = 1;
return v___x_1002_;
}
}
else
{
uint8_t v___x_1003_; 
v___x_1003_ = 0;
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__0___boxed(lean_object* v_x_1004_, lean_object* v_y_1005_){
_start:
{
uint64_t v_x_boxed_1006_; uint64_t v_y_boxed_1007_; uint8_t v_res_1008_; lean_object* v_r_1009_; 
v_x_boxed_1006_ = lean_unbox_uint64(v_x_1004_);
lean_dec_ref(v_x_1004_);
v_y_boxed_1007_ = lean_unbox_uint64(v_y_1005_);
lean_dec_ref(v_y_1005_);
v_res_1008_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__0(v_x_boxed_1006_, v_y_boxed_1007_);
v_r_1009_ = lean_box(v_res_1008_);
return v_r_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__1(lean_object* v_expireTime_1010_, lean_object* v_x_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1012_, 0, v_x_1011_);
lean_ctor_set(v___x_1012_, 1, v_expireTime_1010_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__2(lean_object* v_val_1014_, lean_object* v_inst_1015_, lean_object* v_x_1016_, lean_object* v___y_1017_){
_start:
{
if (lean_obj_tag(v_x_1016_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec_ref(v_inst_1015_);
v_a_1019_ = lean_ctor_get(v_x_1016_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_x_1016_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v_x_1016_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v_x_1016_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
lean_ctor_set_tag(v___x_1021_, 1);
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1045_; 
v_a_1027_ = lean_ctor_get(v_x_1016_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_x_1016_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1029_ = v_x_1016_;
v_isShared_1030_ = v_isSharedCheck_1045_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v_x_1016_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1045_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v_rpcEncode_1032_; lean_object* v_objects_1033_; lean_object* v_expireTime_1034_; lean_object* v___f_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v_fst_1039_; lean_object* v_snd_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1031_ = lean_st_ref_take(v_val_1014_);
v_rpcEncode_1032_ = lean_ctor_get(v_inst_1015_, 0);
lean_inc_ref(v_rpcEncode_1032_);
lean_dec_ref(v_inst_1015_);
v_objects_1033_ = lean_ctor_get(v___x_1031_, 0);
lean_inc_ref(v_objects_1033_);
v_expireTime_1034_ = lean_ctor_get(v___x_1031_, 1);
lean_inc(v_expireTime_1034_);
lean_dec(v___x_1031_);
v___f_1035_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1035_, 0, v_expireTime_1034_);
v___x_1036_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__2___closed__0));
v___x_1037_ = lean_apply_2(v_rpcEncode_1032_, v_a_1027_, v_objects_1033_);
v___x_1038_ = l_Prod_map___redArg(v___x_1036_, v___f_1035_, v___x_1037_);
v_fst_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_fst_1039_);
v_snd_1040_ = lean_ctor_get(v___x_1038_, 1);
lean_inc(v_snd_1040_);
lean_dec_ref(v___x_1038_);
v___x_1041_ = lean_st_ref_put(v_val_1014_, v_snd_1040_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set_tag(v___x_1029_, 0);
lean_ctor_set(v___x_1029_, 0, v_fst_1039_);
v___x_1043_ = v___x_1029_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_fst_1039_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__2___boxed(lean_object* v_val_1046_, lean_object* v_inst_1047_, lean_object* v_x_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__2(v_val_1046_, v_inst_1047_, v_x_1048_, v___y_1049_);
lean_dec_ref(v___y_1049_);
lean_dec(v_val_1046_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__3(lean_object* v___f_1059_, lean_object* v_inst_1060_, lean_object* v_inst_1061_, lean_object* v_method_1062_, lean_object* v_handler_1063_, uint64_t v_seshId_1064_, lean_object* v_j_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_rpcSessions_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_rpcSessions_1068_ = lean_ctor_get(v___y_1066_, 0);
v___x_1069_ = lean_box_uint64(v_seshId_1064_);
lean_inc(v_rpcSessions_1068_);
v___x_1070_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_1059_, v_rpcSessions_1068_, v___x_1069_);
if (lean_obj_tag(v___x_1070_) == 1)
{
lean_object* v_val_1071_; lean_object* v___f_1072_; lean_object* v___x_1073_; lean_object* v_rpcDecode_1074_; lean_object* v_objects_1075_; lean_object* v___x_1076_; 
v_val_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc_n(v_val_1071_, 2);
lean_dec_ref_known(v___x_1070_, 1);
v___f_1072_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_1072_, 0, v_val_1071_);
lean_closure_set(v___f_1072_, 1, v_inst_1060_);
v___x_1073_ = lean_st_ref_get(v_val_1071_);
lean_dec(v_val_1071_);
v_rpcDecode_1074_ = lean_ctor_get(v_inst_1061_, 1);
lean_inc_ref(v_rpcDecode_1074_);
lean_dec_ref(v_inst_1061_);
v_objects_1075_ = lean_ctor_get(v___x_1073_, 0);
lean_inc_ref(v_objects_1075_);
lean_dec(v___x_1073_);
lean_inc(v_j_1065_);
v___x_1076_ = lean_apply_2(v_rpcDecode_1074_, v_j_1065_, v_objects_1075_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1097_; 
lean_dec_ref(v___f_1072_);
lean_dec_ref(v_handler_1063_);
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1097_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1097_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
uint8_t v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1081_ = 3;
v___x_1082_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__0));
v___x_1083_ = 1;
v___x_1084_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_1062_, v___x_1083_);
v___x_1085_ = lean_string_append(v___x_1082_, v___x_1084_);
lean_dec_ref(v___x_1084_);
v___x_1086_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__1));
v___x_1087_ = lean_string_append(v___x_1085_, v___x_1086_);
v___x_1088_ = l_Lean_Json_compress(v_j_1065_);
v___x_1089_ = lean_string_append(v___x_1087_, v___x_1088_);
lean_dec_ref(v___x_1088_);
v___x_1090_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__2));
v___x_1091_ = lean_string_append(v___x_1089_, v___x_1090_);
v___x_1092_ = lean_string_append(v___x_1091_, v_a_1077_);
lean_dec(v_a_1077_);
v___x_1093_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
lean_ctor_set_uint8(v___x_1093_, sizeof(void*)*1, v___x_1081_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set_tag(v___x_1079_, 1);
lean_ctor_set(v___x_1079_, 0, v___x_1093_);
v___x_1095_ = v___x_1079_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1099_; 
lean_dec(v_j_1065_);
lean_dec(v_method_1062_);
v_a_1098_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___x_1076_, 1);
lean_inc_ref(v___y_1066_);
v___x_1099_ = lean_apply_3(v_handler_1063_, v_a_1098_, v___y_1066_, lean_box(0));
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1101_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1099_, 1);
v___x_1101_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_a_1100_, v___f_1072_, v___y_1066_);
return v___x_1101_;
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec_ref(v___f_1072_);
v_a_1102_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1099_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1099_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
}
else
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_dec(v___x_1070_);
lean_dec(v_j_1065_);
lean_dec_ref(v_handler_1063_);
lean_dec(v_method_1062_);
lean_dec_ref(v_inst_1061_);
lean_dec_ref(v_inst_1060_);
v___x_1110_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__4));
v___x_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__3___boxed(lean_object* v___f_1112_, lean_object* v_inst_1113_, lean_object* v_inst_1114_, lean_object* v_method_1115_, lean_object* v_handler_1116_, lean_object* v_seshId_1117_, lean_object* v_j_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
uint64_t v_seshId_boxed_1121_; lean_object* v_res_1122_; 
v_seshId_boxed_1121_ = lean_unbox_uint64(v_seshId_1117_);
lean_dec_ref(v_seshId_1117_);
v_res_1122_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__3(v___f_1112_, v_inst_1113_, v_inst_1114_, v_method_1115_, v_handler_1116_, v_seshId_boxed_1121_, v_j_1118_, v___y_1119_);
lean_dec_ref(v___y_1119_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg(lean_object* v_method_1124_, lean_object* v_inst_1125_, lean_object* v_inst_1126_, lean_object* v_handler_1127_){
_start:
{
lean_object* v___f_1128_; lean_object* v___f_1129_; 
v___f_1128_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___closed__0));
v___f_1129_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___boxed), 9, 5);
lean_closure_set(v___f_1129_, 0, v___f_1128_);
lean_closure_set(v___f_1129_, 1, v_inst_1126_);
lean_closure_set(v___f_1129_, 2, v_inst_1125_);
lean_closure_set(v___f_1129_, 3, v_method_1124_);
lean_closure_set(v___f_1129_, 4, v_handler_1127_);
return v___f_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure(lean_object* v_method_1130_, lean_object* v_paramType_1131_, lean_object* v_respType_1132_, lean_object* v_inst_1133_, lean_object* v_inst_1134_, lean_object* v_handler_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_Server_wrapRpcProcedure___redArg(v_method_1130_, v_inst_1133_, v_inst_1134_, v_handler_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg(lean_object* v_method_1143_, lean_object* v_inst_1144_, lean_object* v_inst_1145_, lean_object* v_handler_1146_){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v_errMsg_1155_; uint8_t v___x_1156_; 
v___x_1148_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__0));
v___x_1149_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__1));
v___x_1150_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__2));
v___x_1151_ = 1;
lean_inc(v_method_1143_);
v___x_1152_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_1143_, v___x_1151_);
v___x_1153_ = lean_string_append(v___x_1150_, v___x_1152_);
lean_dec_ref(v___x_1152_);
v___x_1154_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__3));
v_errMsg_1155_ = lean_string_append(v___x_1153_, v___x_1154_);
v___x_1156_ = l_Lean_initializing();
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_dec_ref(v_handler_1146_);
lean_dec_ref(v_inst_1145_);
lean_dec_ref(v_inst_1144_);
lean_dec(v_method_1143_);
v___x_1157_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__4));
v___x_1158_ = lean_string_append(v_errMsg_1155_, v___x_1157_);
v___x_1159_ = lean_mk_io_user_error(v___x_1158_);
v___x_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
return v___x_1160_;
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1161_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_1162_ = lean_st_ref_get(v___x_1161_);
lean_inc(v_method_1143_);
v___x_1163_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1148_, v___x_1149_, v___x_1162_, v_method_1143_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec_ref(v_errMsg_1155_);
lean_inc(v_method_1143_);
v___x_1164_ = l_Lean_Server_wrapRpcProcedure___redArg(v_method_1143_, v_inst_1144_, v_inst_1145_, v_handler_1146_);
v___x_1165_ = lean_st_ref_take(v___x_1161_);
v___x_1166_ = l_Lean_PersistentHashMap_insert___redArg(v___x_1148_, v___x_1149_, v___x_1165_, v_method_1143_, v___x_1164_);
v___x_1167_ = lean_st_ref_put(v___x_1161_, v___x_1166_);
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
else
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
lean_dec_ref(v_handler_1146_);
lean_dec_ref(v_inst_1145_);
lean_dec_ref(v_inst_1144_);
lean_dec(v_method_1143_);
v___x_1169_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__5));
v___x_1170_ = lean_string_append(v_errMsg_1155_, v___x_1169_);
v___x_1171_ = lean_mk_io_user_error(v___x_1170_);
v___x_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
return v___x_1172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg___boxed(lean_object* v_method_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_, lean_object* v_handler_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_Server_registerBuiltinRpcProcedure___redArg(v_method_1173_, v_inst_1174_, v_inst_1175_, v_handler_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure(lean_object* v_method_1179_, lean_object* v_paramType_1180_, lean_object* v_respType_1181_, lean_object* v_inst_1182_, lean_object* v_inst_1183_, lean_object* v_handler_1184_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_Server_registerBuiltinRpcProcedure___redArg(v_method_1179_, v_inst_1182_, v_inst_1183_, v_handler_1184_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___boxed(lean_object* v_method_1187_, lean_object* v_paramType_1188_, lean_object* v_respType_1189_, lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_handler_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Server_registerBuiltinRpcProcedure(v_method_1187_, v_paramType_1188_, v_respType_1189_, v_inst_1190_, v_inst_1191_, v_handler_1192_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(lean_object* v_e_1195_, lean_object* v___y_1196_){
_start:
{
uint8_t v___x_1198_; 
v___x_1198_ = l_Lean_Expr_hasMVar(v_e_1195_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; 
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v_e_1195_);
return v___x_1199_;
}
else
{
lean_object* v___x_1200_; lean_object* v_mctx_1201_; lean_object* v___x_1202_; lean_object* v_fst_1203_; lean_object* v_snd_1204_; lean_object* v___x_1205_; lean_object* v_cache_1206_; lean_object* v_zetaDeltaFVarIds_1207_; lean_object* v_postponed_1208_; lean_object* v_diag_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1218_; 
v___x_1200_ = lean_st_ref_get(v___y_1196_);
v_mctx_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc_ref(v_mctx_1201_);
lean_dec(v___x_1200_);
v___x_1202_ = l_Lean_instantiateMVarsCore(v_mctx_1201_, v_e_1195_);
v_fst_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_fst_1203_);
v_snd_1204_ = lean_ctor_get(v___x_1202_, 1);
lean_inc(v_snd_1204_);
lean_dec_ref(v___x_1202_);
v___x_1205_ = lean_st_ref_take(v___y_1196_);
v_cache_1206_ = lean_ctor_get(v___x_1205_, 1);
v_zetaDeltaFVarIds_1207_ = lean_ctor_get(v___x_1205_, 2);
v_postponed_1208_ = lean_ctor_get(v___x_1205_, 3);
v_diag_1209_ = lean_ctor_get(v___x_1205_, 4);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; 
v_unused_1219_ = lean_ctor_get(v___x_1205_, 0);
lean_dec(v_unused_1219_);
v___x_1211_ = v___x_1205_;
v_isShared_1212_ = v_isSharedCheck_1218_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_diag_1209_);
lean_inc(v_postponed_1208_);
lean_inc(v_zetaDeltaFVarIds_1207_);
lean_inc(v_cache_1206_);
lean_dec(v___x_1205_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1218_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 0, v_snd_1204_);
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_snd_1204_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_cache_1206_);
lean_ctor_set(v_reuseFailAlloc_1217_, 2, v_zetaDeltaFVarIds_1207_);
lean_ctor_set(v_reuseFailAlloc_1217_, 3, v_postponed_1208_);
lean_ctor_set(v_reuseFailAlloc_1217_, 4, v_diag_1209_);
v___x_1214_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_st_ref_put(v___y_1196_, v___x_1214_);
v___x_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1216_, 0, v_fst_1203_);
return v___x_1216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg___boxed(lean_object* v_e_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(v_e_1220_, v___y_1221_);
lean_dec(v___y_1221_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0(lean_object* v_e_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(v_e_1224_, v___y_1228_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___boxed(lean_object* v_e_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0(v_e_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg(lean_object* v_a_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg___boxed(lean_object* v_a_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg(v_a_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1(lean_object* v_00_u03b1_1260_, lean_object* v_a_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___boxed(lean_object* v_00_u03b1_1270_, lean_object* v_a_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1(v_00_u03b1_1270_, v_a_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
return v_res_1279_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_);
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
return v___x_1281_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0);
v___x_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(lean_object* v_env_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; lean_object* v_nextMacroScope_1288_; lean_object* v_ngen_1289_; lean_object* v_auxDeclNGen_1290_; lean_object* v_traceState_1291_; lean_object* v_recordedDeps_1292_; lean_object* v_messages_1293_; lean_object* v_infoState_1294_; lean_object* v_snapshotTasks_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1306_; 
v___x_1287_ = lean_st_ref_take(v___y_1285_);
v_nextMacroScope_1288_ = lean_ctor_get(v___x_1287_, 1);
v_ngen_1289_ = lean_ctor_get(v___x_1287_, 2);
v_auxDeclNGen_1290_ = lean_ctor_get(v___x_1287_, 3);
v_traceState_1291_ = lean_ctor_get(v___x_1287_, 4);
v_recordedDeps_1292_ = lean_ctor_get(v___x_1287_, 6);
v_messages_1293_ = lean_ctor_get(v___x_1287_, 7);
v_infoState_1294_ = lean_ctor_get(v___x_1287_, 8);
v_snapshotTasks_1295_ = lean_ctor_get(v___x_1287_, 9);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1306_ == 0)
{
lean_object* v_unused_1307_; lean_object* v_unused_1308_; 
v_unused_1307_ = lean_ctor_get(v___x_1287_, 5);
lean_dec(v_unused_1307_);
v_unused_1308_ = lean_ctor_get(v___x_1287_, 0);
lean_dec(v_unused_1308_);
v___x_1297_ = v___x_1287_;
v_isShared_1298_ = v_isSharedCheck_1306_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_snapshotTasks_1295_);
lean_inc(v_infoState_1294_);
lean_inc(v_messages_1293_);
lean_inc(v_recordedDeps_1292_);
lean_inc(v_traceState_1291_);
lean_inc(v_auxDeclNGen_1290_);
lean_inc(v_ngen_1289_);
lean_inc(v_nextMacroScope_1288_);
lean_dec(v___x_1287_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1306_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
v___x_1299_ = lean_box(0);
v___x_1300_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 5, v___x_1300_);
lean_ctor_set(v___x_1297_, 0, v_env_1284_);
v___x_1302_ = v___x_1297_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_env_1284_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_nextMacroScope_1288_);
lean_ctor_set(v_reuseFailAlloc_1305_, 2, v_ngen_1289_);
lean_ctor_set(v_reuseFailAlloc_1305_, 3, v_auxDeclNGen_1290_);
lean_ctor_set(v_reuseFailAlloc_1305_, 4, v_traceState_1291_);
lean_ctor_set(v_reuseFailAlloc_1305_, 5, v___x_1300_);
lean_ctor_set(v_reuseFailAlloc_1305_, 6, v_recordedDeps_1292_);
lean_ctor_set(v_reuseFailAlloc_1305_, 7, v_messages_1293_);
lean_ctor_set(v_reuseFailAlloc_1305_, 8, v_infoState_1294_);
lean_ctor_set(v_reuseFailAlloc_1305_, 9, v_snapshotTasks_1295_);
v___x_1302_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = lean_st_ref_put(v___y_1285_, v___x_1302_);
v___x_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1299_);
return v___x_1304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___boxed(lean_object* v_env_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(v_env_1309_, v___y_1310_);
lean_dec(v___y_1310_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2(lean_object* v_env_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(v_env_1313_, v___y_1315_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___boxed(lean_object* v_env_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2(v_env_1318_, v___y_1319_, v___y_1320_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
return v_res_1322_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_registerRpcProcedure___lam__0(lean_object* v_x_1323_){
_start:
{
uint8_t v___x_1324_; 
v___x_1324_ = 0;
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__0___boxed(lean_object* v_x_1325_){
_start:
{
uint8_t v_res_1326_; lean_object* v_r_1327_; 
v_res_1326_ = l_Lean_Server_registerRpcProcedure___lam__0(v_x_1325_);
lean_dec(v_x_1325_);
v_r_1327_ = lean_box(v_res_1326_);
return v_r_1327_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__3));
v___x_1333_ = l_String_toRawSubstring_x27(v___x_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__1(lean_object* v___x_1344_, lean_object* v___x_1345_, lean_object* v_method_1346_, lean_object* v___x_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_toCold_1355_; lean_object* v_ref_1356_; lean_object* v_quotContext_1357_; lean_object* v_currMacroScope_1358_; uint8_t v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___y_1378_; lean_object* v___x_1392_; 
v_toCold_1355_ = lean_ctor_get(v___y_1352_, 0);
v_ref_1356_ = lean_ctor_get(v___y_1352_, 2);
v_quotContext_1357_ = lean_ctor_get(v_toCold_1355_, 8);
v_currMacroScope_1358_ = lean_ctor_get(v_toCold_1355_, 9);
v___x_1359_ = 0;
v___x_1360_ = l_Lean_SourceInfo_fromRef(v_ref_1356_, v___x_1359_);
v___x_1361_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__0));
v___x_1362_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__1));
v___x_1363_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__2));
lean_inc_ref_n(v___x_1344_, 2);
v___x_1364_ = l_Lean_Name_mkStr4(v___x_1344_, v___x_1361_, v___x_1362_, v___x_1363_);
v___x_1365_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__3));
v___x_1366_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___lam__1___closed__4, &l_Lean_Server_registerRpcProcedure___lam__1___closed__4_once, _init_l_Lean_Server_registerRpcProcedure___lam__1___closed__4);
v___x_1367_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__5));
lean_inc(v_currMacroScope_1358_);
lean_inc(v_quotContext_1357_);
v___x_1368_ = l_Lean_addMacroScope(v_quotContext_1357_, v___x_1367_, v_currMacroScope_1358_);
v___x_1369_ = l_Lean_Name_mkStr3(v___x_1344_, v___x_1345_, v___x_1365_);
v___x_1370_ = lean_box(0);
lean_inc(v___x_1369_);
v___x_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1369_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1369_);
v___x_1373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
lean_ctor_set(v___x_1373_, 1, v___x_1370_);
v___x_1374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1371_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
lean_inc(v___x_1360_);
v___x_1375_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1360_);
lean_ctor_set(v___x_1375_, 1, v___x_1366_);
lean_ctor_set(v___x_1375_, 2, v___x_1368_);
lean_ctor_set(v___x_1375_, 3, v___x_1374_);
v___x_1376_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__7));
lean_inc(v_method_1346_);
v___x_1392_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_1370_, v_method_1346_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v___x_1393_; 
lean_inc(v_method_1346_);
v___x_1393_ = l_Lean_quoteNameMk(v_method_1346_);
v___y_1378_ = v___x_1393_;
goto v___jp_1377_;
}
else
{
lean_object* v_val_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v_val_1394_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_val_1394_);
lean_dec_ref_known(v___x_1392_, 1);
v___x_1395_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__10));
lean_inc_ref(v___x_1344_);
v___x_1396_ = l_Lean_Name_mkStr4(v___x_1344_, v___x_1361_, v___x_1362_, v___x_1395_);
v___x_1397_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__11));
v___x_1398_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__12));
v___x_1399_ = lean_string_intercalate(v___x_1398_, v_val_1394_);
v___x_1400_ = lean_string_append(v___x_1397_, v___x_1399_);
lean_dec_ref(v___x_1399_);
v___x_1401_ = lean_box(2);
v___x_1402_ = l_Lean_Syntax_mkNameLit(v___x_1400_, v___x_1401_);
v___x_1403_ = lean_unsigned_to_nat(1u);
v___x_1404_ = lean_mk_empty_array_with_capacity(v___x_1403_);
v___x_1405_ = lean_array_push(v___x_1404_, v___x_1402_);
v___x_1406_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1401_);
lean_ctor_set(v___x_1406_, 1, v___x_1396_);
lean_ctor_set(v___x_1406_, 2, v___x_1405_);
v___y_1378_ = v___x_1406_;
goto v___jp_1377_;
}
v___jp_1377_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; lean_object* v___x_1389_; 
v___x_1379_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__8));
v___x_1380_ = l_Lean_Name_mkStr4(v___x_1344_, v___x_1361_, v___x_1362_, v___x_1379_);
v___x_1381_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__9));
lean_inc_n(v___x_1360_, 3);
v___x_1382_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1360_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
v___x_1383_ = l_Lean_Syntax_node1(v___x_1360_, v___x_1380_, v___x_1382_);
v___x_1384_ = l_Lean_mkIdent(v_method_1346_);
lean_inc(v___x_1383_);
v___x_1385_ = l_Lean_Syntax_node4(v___x_1360_, v___x_1376_, v___y_1378_, v___x_1383_, v___x_1383_, v___x_1384_);
v___x_1386_ = l_Lean_Syntax_node2(v___x_1360_, v___x_1364_, v___x_1375_, v___x_1385_);
v___x_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1347_);
v___x_1388_ = 1;
v___x_1389_ = l_Lean_Elab_Term_elabTerm(v___x_1386_, v___x_1387_, v___x_1388_, v___x_1388_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec_ref(v___y_1352_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1391_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v___x_1389_, 1);
v___x_1391_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(v_a_1390_, v___y_1351_);
return v___x_1391_;
}
else
{
return v___x_1389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__1___boxed(lean_object* v___x_1407_, lean_object* v___x_1408_, lean_object* v_method_1409_, lean_object* v___x_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_Server_registerRpcProcedure___lam__1(v___x_1407_, v___x_1408_, v_method_1409_, v___x_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
return v_res_1418_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_);
v___x_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
return v___x_1420_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1421_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1422_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0);
v___x_1423_ = lean_unsigned_to_nat(0u);
v___x_1424_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
lean_ctor_set(v___x_1424_, 2, v___x_1423_);
lean_ctor_set(v___x_1424_, 3, v___x_1423_);
lean_ctor_set(v___x_1424_, 4, v___x_1422_);
lean_ctor_set(v___x_1424_, 5, v___x_1422_);
lean_ctor_set(v___x_1424_, 6, v___x_1422_);
lean_ctor_set(v___x_1424_, 7, v___x_1422_);
lean_ctor_set(v___x_1424_, 8, v___x_1422_);
lean_ctor_set(v___x_1424_, 9, v___x_1422_);
lean_ctor_set(v___x_1424_, 10, v___x_1422_);
lean_ctor_set(v___x_1424_, 11, v___x_1421_);
return v___x_1424_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = lean_unsigned_to_nat(32u);
v___x_1426_ = lean_mk_empty_array_with_capacity(v___x_1425_);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
return v___x_1427_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3(void){
_start:
{
size_t v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1428_ = ((size_t)5ULL);
v___x_1429_ = lean_unsigned_to_nat(0u);
v___x_1430_ = lean_unsigned_to_nat(32u);
v___x_1431_ = lean_mk_empty_array_with_capacity(v___x_1430_);
v___x_1432_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2);
v___x_1433_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
lean_ctor_set(v___x_1433_, 1, v___x_1431_);
lean_ctor_set(v___x_1433_, 2, v___x_1429_);
lean_ctor_set(v___x_1433_, 3, v___x_1429_);
lean_ctor_set_usize(v___x_1433_, 4, v___x_1428_);
return v___x_1433_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1434_ = lean_box(1);
v___x_1435_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3);
v___x_1436_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0);
v___x_1437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
lean_ctor_set(v___x_1437_, 1, v___x_1435_);
lean_ctor_set(v___x_1437_, 2, v___x_1434_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3(lean_object* v_msgData_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v___x_1442_; lean_object* v_toCold_1443_; lean_object* v_env_1444_; lean_object* v_options_1445_; uint8_t v___x_1446_; lean_object* v_env_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1442_ = lean_st_ref_get(v___y_1440_);
v_toCold_1443_ = lean_ctor_get(v___y_1439_, 0);
v_env_1444_ = lean_ctor_get(v___x_1442_, 0);
lean_inc_ref(v_env_1444_);
lean_dec(v___x_1442_);
v_options_1445_ = lean_ctor_get(v_toCold_1443_, 2);
v___x_1446_ = 0;
v_env_1447_ = l_Lean_Environment_setRecordingDeps(v_env_1444_, v___x_1446_);
v___x_1448_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1);
v___x_1449_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4);
lean_inc_ref(v_options_1445_);
v___x_1450_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1450_, 0, v_env_1447_);
lean_ctor_set(v___x_1450_, 1, v___x_1448_);
lean_ctor_set(v___x_1450_, 2, v___x_1449_);
lean_ctor_set(v___x_1450_, 3, v_options_1445_);
v___x_1451_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
lean_ctor_set(v___x_1451_, 1, v_msgData_1438_);
v___x_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___boxed(lean_object* v_msgData_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3(v_msgData_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(lean_object* v_msg_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_ref_1462_; lean_object* v___x_1463_; lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1472_; 
v_ref_1462_ = lean_ctor_get(v___y_1459_, 2);
v___x_1463_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3(v_msg_1458_, v___y_1459_, v___y_1460_);
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1466_ = v___x_1463_;
v_isShared_1467_ = v_isSharedCheck_1472_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1463_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1472_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; lean_object* v___x_1470_; 
lean_inc(v_ref_1462_);
v___x_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1468_, 0, v_ref_1462_);
lean_ctor_set(v___x_1468_, 1, v_a_1464_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set_tag(v___x_1466_, 1);
lean_ctor_set(v___x_1466_, 0, v___x_1468_);
v___x_1470_ = v___x_1466_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg___boxed(lean_object* v_msg_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v_msg_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
return v_res_1477_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__3(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = lean_box(0);
v___x_1483_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1));
v___x_1484_ = l_Lean_mkConst(v___x_1483_, v___x_1482_);
return v___x_1484_;
}
}
static uint64_t _init_l_Lean_Server_registerRpcProcedure___closed__8(void){
_start:
{
lean_object* v___x_1504_; uint64_t v___x_1505_; 
v___x_1504_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__7));
v___x_1505_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1504_);
return v___x_1505_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__9(void){
_start:
{
uint64_t v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = lean_uint64_once(&l_Lean_Server_registerRpcProcedure___closed__8, &l_Lean_Server_registerRpcProcedure___closed__8_once, _init_l_Lean_Server_registerRpcProcedure___closed__8);
v___x_1507_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__7));
v___x_1508_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
lean_ctor_set_uint64(v___x_1508_, sizeof(void*)*1, v___x_1506_);
return v___x_1508_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__10(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_);
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
return v___x_1510_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__11(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1511_ = lean_box(1);
v___x_1512_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3);
v___x_1513_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__10, &l_Lean_Server_registerRpcProcedure___closed__10_once, _init_l_Lean_Server_registerRpcProcedure___closed__10);
v___x_1514_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v___x_1512_);
lean_ctor_set(v___x_1514_, 2, v___x_1511_);
return v___x_1514_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__12(void){
_start:
{
uint8_t v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1515_ = 1;
v___x_1516_ = lean_unsigned_to_nat(0u);
v___x_1517_ = lean_box(0);
v___x_1518_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__4));
v___x_1519_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__11, &l_Lean_Server_registerRpcProcedure___closed__11_once, _init_l_Lean_Server_registerRpcProcedure___closed__11);
v___x_1520_ = lean_box(1);
v___x_1521_ = 0;
v___x_1522_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__9, &l_Lean_Server_registerRpcProcedure___closed__9_once, _init_l_Lean_Server_registerRpcProcedure___closed__9);
v___x_1523_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
lean_ctor_set(v___x_1523_, 1, v___x_1520_);
lean_ctor_set(v___x_1523_, 2, v___x_1519_);
lean_ctor_set(v___x_1523_, 3, v___x_1518_);
lean_ctor_set(v___x_1523_, 4, v___x_1517_);
lean_ctor_set(v___x_1523_, 5, v___x_1516_);
lean_ctor_set(v___x_1523_, 6, v___x_1517_);
lean_ctor_set_uint8(v___x_1523_, sizeof(void*)*7, v___x_1521_);
lean_ctor_set_uint8(v___x_1523_, sizeof(void*)*7 + 1, v___x_1521_);
lean_ctor_set_uint8(v___x_1523_, sizeof(void*)*7 + 2, v___x_1521_);
lean_ctor_set_uint8(v___x_1523_, sizeof(void*)*7 + 3, v___x_1515_);
return v___x_1523_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__13(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1524_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1525_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__10, &l_Lean_Server_registerRpcProcedure___closed__10_once, _init_l_Lean_Server_registerRpcProcedure___closed__10);
v___x_1526_ = lean_unsigned_to_nat(0u);
v___x_1527_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
lean_ctor_set(v___x_1527_, 2, v___x_1526_);
lean_ctor_set(v___x_1527_, 3, v___x_1526_);
lean_ctor_set(v___x_1527_, 4, v___x_1525_);
lean_ctor_set(v___x_1527_, 5, v___x_1525_);
lean_ctor_set(v___x_1527_, 6, v___x_1525_);
lean_ctor_set(v___x_1527_, 7, v___x_1525_);
lean_ctor_set(v___x_1527_, 8, v___x_1525_);
lean_ctor_set(v___x_1527_, 9, v___x_1525_);
lean_ctor_set(v___x_1527_, 10, v___x_1525_);
lean_ctor_set(v___x_1527_, 11, v___x_1524_);
return v___x_1527_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__14(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__10, &l_Lean_Server_registerRpcProcedure___closed__10_once, _init_l_Lean_Server_registerRpcProcedure___closed__10);
v___x_1529_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
lean_ctor_set(v___x_1529_, 2, v___x_1528_);
lean_ctor_set(v___x_1529_, 3, v___x_1528_);
lean_ctor_set(v___x_1529_, 4, v___x_1528_);
lean_ctor_set(v___x_1529_, 5, v___x_1528_);
return v___x_1529_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__15(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__10, &l_Lean_Server_registerRpcProcedure___closed__10_once, _init_l_Lean_Server_registerRpcProcedure___closed__10);
v___x_1531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
lean_ctor_set(v___x_1531_, 2, v___x_1530_);
lean_ctor_set(v___x_1531_, 3, v___x_1530_);
lean_ctor_set(v___x_1531_, 4, v___x_1530_);
return v___x_1531_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__16(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1532_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__15, &l_Lean_Server_registerRpcProcedure___closed__15_once, _init_l_Lean_Server_registerRpcProcedure___closed__15);
v___x_1533_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3);
v___x_1534_ = lean_box(1);
v___x_1535_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__14, &l_Lean_Server_registerRpcProcedure___closed__14_once, _init_l_Lean_Server_registerRpcProcedure___closed__14);
v___x_1536_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__13, &l_Lean_Server_registerRpcProcedure___closed__13_once, _init_l_Lean_Server_registerRpcProcedure___closed__13);
v___x_1537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
lean_ctor_set(v___x_1537_, 1, v___x_1535_);
lean_ctor_set(v___x_1537_, 2, v___x_1534_);
lean_ctor_set(v___x_1537_, 3, v___x_1533_);
lean_ctor_set(v___x_1537_, 4, v___x_1532_);
return v___x_1537_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__17(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__10, &l_Lean_Server_registerRpcProcedure___closed__10_once, _init_l_Lean_Server_registerRpcProcedure___closed__10);
v___x_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
return v___x_1539_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__19(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__18));
v___x_1542_ = l_Lean_stringToMessageData(v___x_1541_);
return v___x_1542_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__20(void){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__3));
v___x_1544_ = l_Lean_stringToMessageData(v___x_1543_);
return v___x_1544_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__21(void){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__5));
v___x_1546_ = l_Lean_stringToMessageData(v___x_1545_);
return v___x_1546_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__23(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__22));
v___x_1549_ = l_Lean_stringToMessageData(v___x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure(lean_object* v_method_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v_env_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___x_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1625_ = lean_box(0);
v___x_1626_ = lean_st_ref_get(v_a_1552_);
v_env_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc_ref(v_env_1627_);
lean_dec(v___x_1626_);
v___x_1628_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__19, &l_Lean_Server_registerRpcProcedure___closed__19_once, _init_l_Lean_Server_registerRpcProcedure___closed__19);
lean_inc(v_method_1550_);
v___x_1629_ = l_Lean_MessageData_ofName(v_method_1550_);
v___x_1630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1628_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__20, &l_Lean_Server_registerRpcProcedure___closed__20_once, _init_l_Lean_Server_registerRpcProcedure___closed__20);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1643_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_1644_ = lean_st_ref_get(v___x_1643_);
v___x_1645_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(v___x_1644_, v_method_1550_);
lean_dec(v___x_1644_);
if (v___x_1645_ == 0)
{
v___y_1634_ = v_a_1551_;
v___y_1635_ = v_a_1552_;
goto v___jp_1633_;
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_dec_ref(v_env_1627_);
lean_dec(v_method_1550_);
v___x_1646_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__23, &l_Lean_Server_registerRpcProcedure___closed__23_once, _init_l_Lean_Server_registerRpcProcedure___closed__23);
v___x_1647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1632_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v___x_1647_, v_a_1551_, v_a_1552_);
return v___x_1648_;
}
v___jp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___f_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; uint8_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1557_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__2));
lean_inc_n(v_method_1550_, 2);
v___x_1558_ = l_Lean_Name_append(v_method_1550_, v___x_1557_);
v___x_1559_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_1560_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_1561_ = lean_box(0);
v___x_1562_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__3, &l_Lean_Server_registerRpcProcedure___closed__3_once, _init_l_Lean_Server_registerRpcProcedure___closed__3);
v___f_1563_ = lean_alloc_closure((void*)(l_Lean_Server_registerRpcProcedure___lam__1___boxed), 11, 4);
lean_closure_set(v___f_1563_, 0, v___x_1559_);
lean_closure_set(v___f_1563_, 1, v___x_1560_);
lean_closure_set(v___f_1563_, 2, v_method_1550_);
lean_closure_set(v___f_1563_, 3, v___x_1562_);
v___x_1564_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___boxed), 9, 2);
lean_closure_set(v___x_1564_, 0, lean_box(0));
lean_closure_set(v___x_1564_, 1, v___f_1563_);
v___x_1565_ = 1;
v___x_1566_ = 0;
v___x_1567_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__5));
v___x_1568_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__6));
v___x_1569_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__12, &l_Lean_Server_registerRpcProcedure___closed__12_once, _init_l_Lean_Server_registerRpcProcedure___closed__12);
v___x_1570_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__16, &l_Lean_Server_registerRpcProcedure___closed__16_once, _init_l_Lean_Server_registerRpcProcedure___closed__16);
v___x_1571_ = lean_st_mk_ref(v___x_1570_);
v___x_1572_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_1564_, v___x_1567_, v___x_1568_, v___x_1569_, v___x_1571_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v_fst_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1615_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v___x_1572_, 1);
v_fst_1574_ = lean_ctor_get(v_a_1573_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_a_1573_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; 
v_unused_1616_ = lean_ctor_get(v_a_1573_, 1);
lean_dec(v_unused_1616_);
v___x_1576_ = v_a_1573_;
v_isShared_1577_ = v_isSharedCheck_1615_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_fst_1574_);
lean_dec(v_a_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1615_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; lean_object* v___x_1583_; 
v___x_1578_ = lean_st_ref_get(v___x_1571_);
lean_dec(v___x_1571_);
lean_dec(v___x_1578_);
lean_inc_n(v___x_1558_, 2);
v___x_1579_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1558_);
lean_ctor_set(v___x_1579_, 1, v___x_1561_);
lean_ctor_set(v___x_1579_, 2, v___x_1562_);
v___x_1580_ = lean_box(0);
v___x_1581_ = 1;
if (v_isShared_1577_ == 0)
{
lean_ctor_set_tag(v___x_1576_, 1);
lean_ctor_set(v___x_1576_, 1, v___x_1561_);
lean_ctor_set(v___x_1576_, 0, v___x_1558_);
v___x_1583_ = v___x_1576_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v___x_1561_);
v___x_1583_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1584_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1584_, 0, v___x_1579_);
lean_ctor_set(v___x_1584_, 1, v_fst_1574_);
lean_ctor_set(v___x_1584_, 2, v___x_1580_);
lean_ctor_set(v___x_1584_, 3, v___x_1583_);
lean_ctor_set_uint8(v___x_1584_, sizeof(void*)*4, v___x_1581_);
v___x_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
lean_inc_ref(v___x_1585_);
v___x_1586_ = l_Lean_addDecl(v___x_1585_, v___x_1566_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v___x_1587_; lean_object* v_env_1588_; lean_object* v_nextMacroScope_1589_; lean_object* v_ngen_1590_; lean_object* v_auxDeclNGen_1591_; lean_object* v_traceState_1592_; lean_object* v_recordedDeps_1593_; lean_object* v_messages_1594_; lean_object* v_infoState_1595_; lean_object* v_snapshotTasks_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1612_; 
lean_dec_ref_known(v___x_1586_, 1);
v___x_1587_ = lean_st_ref_take(v___y_1556_);
v_env_1588_ = lean_ctor_get(v___x_1587_, 0);
v_nextMacroScope_1589_ = lean_ctor_get(v___x_1587_, 1);
v_ngen_1590_ = lean_ctor_get(v___x_1587_, 2);
v_auxDeclNGen_1591_ = lean_ctor_get(v___x_1587_, 3);
v_traceState_1592_ = lean_ctor_get(v___x_1587_, 4);
v_recordedDeps_1593_ = lean_ctor_get(v___x_1587_, 6);
v_messages_1594_ = lean_ctor_get(v___x_1587_, 7);
v_infoState_1595_ = lean_ctor_get(v___x_1587_, 8);
v_snapshotTasks_1596_ = lean_ctor_get(v___x_1587_, 9);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; 
v_unused_1613_ = lean_ctor_get(v___x_1587_, 5);
lean_dec(v_unused_1613_);
v___x_1598_ = v___x_1587_;
v_isShared_1599_ = v_isSharedCheck_1612_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_snapshotTasks_1596_);
lean_inc(v_infoState_1595_);
lean_inc(v_messages_1594_);
lean_inc(v_recordedDeps_1593_);
lean_inc(v_traceState_1592_);
lean_inc(v_auxDeclNGen_1591_);
lean_inc(v_ngen_1590_);
lean_inc(v_nextMacroScope_1589_);
lean_inc(v_env_1588_);
lean_dec(v___x_1587_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1612_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1603_; 
lean_inc(v___x_1558_);
v___x_1600_ = l_Lean_markMeta(v_env_1588_, v___x_1558_);
v___x_1601_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__17, &l_Lean_Server_registerRpcProcedure___closed__17_once, _init_l_Lean_Server_registerRpcProcedure___closed__17);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 5, v___x_1601_);
lean_ctor_set(v___x_1598_, 0, v___x_1600_);
v___x_1603_ = v___x_1598_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_nextMacroScope_1589_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v_ngen_1590_);
lean_ctor_set(v_reuseFailAlloc_1611_, 3, v_auxDeclNGen_1591_);
lean_ctor_set(v_reuseFailAlloc_1611_, 4, v_traceState_1592_);
lean_ctor_set(v_reuseFailAlloc_1611_, 5, v___x_1601_);
lean_ctor_set(v_reuseFailAlloc_1611_, 6, v_recordedDeps_1593_);
lean_ctor_set(v_reuseFailAlloc_1611_, 7, v_messages_1594_);
lean_ctor_set(v_reuseFailAlloc_1611_, 8, v_infoState_1595_);
lean_ctor_set(v_reuseFailAlloc_1611_, 9, v_snapshotTasks_1596_);
v___x_1603_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = lean_st_ref_put(v___y_1556_, v___x_1603_);
v___x_1605_ = l_Lean_compileDecl(v___x_1585_, v___x_1565_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v___x_1606_; lean_object* v_env_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
lean_dec_ref_known(v___x_1605_, 1);
v___x_1606_ = lean_st_ref_get(v___y_1556_);
v_env_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc_ref(v_env_1607_);
lean_dec(v___x_1606_);
v___x_1608_ = l_Lean_Server_userRpcProcedures;
v___x_1609_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1608_, v_env_1607_, v_method_1550_, v___x_1558_, v___x_1566_);
v___x_1610_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(v___x_1609_, v___y_1556_);
return v___x_1610_;
}
else
{
lean_dec(v___x_1558_);
lean_dec(v_method_1550_);
return v___x_1605_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1585_, 1);
lean_dec(v___x_1558_);
lean_dec(v_method_1550_);
return v___x_1586_;
}
}
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec(v___x_1571_);
lean_dec(v___x_1558_);
lean_dec(v_method_1550_);
v_a_1617_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1572_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1572_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
v___jp_1633_:
{
lean_object* v___x_1636_; lean_object* v_toEnvExtension_1637_; lean_object* v_asyncMode_1638_; uint8_t v___x_1639_; 
v___x_1636_ = l_Lean_Server_userRpcProcedures;
v_toEnvExtension_1637_ = lean_ctor_get(v___x_1636_, 0);
v_asyncMode_1638_ = lean_ctor_get(v_toEnvExtension_1637_, 2);
lean_inc(v_method_1550_);
v___x_1639_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_1625_, v___x_1636_, v_env_1627_, v_method_1550_, v_asyncMode_1638_);
if (v___x_1639_ == 0)
{
lean_dec_ref_known(v___x_1632_, 2);
v___y_1555_ = v___y_1634_;
v___y_1556_ = v___y_1635_;
goto v___jp_1554_;
}
else
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
lean_dec(v_method_1550_);
v___x_1640_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__21, &l_Lean_Server_registerRpcProcedure___closed__21_once, _init_l_Lean_Server_registerRpcProcedure___closed__21);
v___x_1641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1632_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v___x_1641_, v___y_1634_, v___y_1635_);
return v___x_1642_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___boxed(lean_object* v_method_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_Server_registerRpcProcedure(v_method_1649_, v_a_1650_, v_a_1651_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3(lean_object* v_00_u03b1_1654_, lean_object* v_msg_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v_msg_1655_, v___y_1656_, v___y_1657_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___boxed(lean_object* v_00_u03b1_1660_, lean_object* v_msg_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3(v_00_u03b1_1660_, v_msg_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(lean_object* v___x_1666_, lean_object* v_decl_1667_, lean_object* v_x_1668_, uint8_t v_attrKind_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v___x_1673_; 
lean_inc(v_decl_1667_);
v___x_1673_ = l_Lean_ensureAttrDeclIsMeta(v___x_1666_, v_decl_1667_, v_attrKind_1669_, v___y_1670_, v___y_1671_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v___x_1674_; 
lean_dec_ref_known(v___x_1673_, 1);
v___x_1674_ = l_Lean_Server_registerRpcProcedure(v_decl_1667_, v___y_1670_, v___y_1671_);
return v___x_1674_;
}
else
{
lean_dec(v_decl_1667_);
return v___x_1673_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed(lean_object* v___x_1675_, lean_object* v_decl_1676_, lean_object* v_x_1677_, lean_object* v_attrKind_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
uint8_t v_attrKind_boxed_1682_; lean_object* v_res_1683_; 
v_attrKind_boxed_1682_ = lean_unbox(v_attrKind_1678_);
v_res_1683_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(v___x_1675_, v_decl_1676_, v_x_1677_, v_attrKind_boxed_1682_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v_x_1677_);
return v_res_1683_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_));
v___x_1686_ = l_Lean_stringToMessageData(v___x_1685_);
return v___x_1686_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_));
v___x_1689_ = l_Lean_stringToMessageData(v___x_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(lean_object* v___x_1690_, lean_object* v_decl_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1695_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_);
v___x_1696_ = l_Lean_MessageData_ofName(v___x_1690_);
v___x_1697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1695_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1698_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_);
v___x_1699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1697_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v___x_1699_, v___y_1692_, v___y_1693_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed(lean_object* v___x_1701_, lean_object* v_decl_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(v___x_1701_, v_decl_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v_decl_1702_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__31_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_));
v___x_1787_ = l_Lean_registerBuiltinAttribute(v___x_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed(lean_object* v_a_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_();
return v_res_1789_;
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
