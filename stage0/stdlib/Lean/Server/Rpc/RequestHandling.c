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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Lean_Server_instInhabitedRpcProcedure_default___lam__0(uint64_t v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = l_Lean_Server_instInhabitedRequestError_default;
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Server_instInhabitedRpcProcedure_default___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_1_ = stack[0].m_num;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v_res_7_;
v_res_7_ = l_Lean_Server_instInhabitedRpcProcedure_default___lam__0(v_x_1_, v___y_2_, v___y_3_);
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRpcProcedure_default___lam__0___boxed(lean_object* v_x_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
uint64_t v_x_55__boxed_12_; lean_object* v_res_13_; 
v_x_55__boxed_12_ = lean_unbox_uint64(v_x_8_);
lean_dec_ref(v_x_8_);
v_res_13_ = l_Lean_Server_instInhabitedRpcProcedure_default___lam__0(v_x_55__boxed_12_, v___y_9_, v___y_10_);
lean_dec_ref(v___y_10_);
lean_dec(v___y_9_);
return v_res_13_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_17_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_);
v___x_19_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
return v___x_19_;
}
}
lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_21_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_);
v___x_22_ = lean_st_mk_ref(v___x_21_);
v___x_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_24_;
v_res_24_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_();
stack->m_obj
 = v_res_24_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2____boxed(lean_object* v_a_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_();
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_27_, lean_object* v_x_28_){
_start:
{
if (lean_obj_tag(v_x_28_) == 0)
{
lean_object* v_k_29_; lean_object* v_v_30_; lean_object* v_l_31_; lean_object* v_r_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v_k_29_ = lean_ctor_get(v_x_28_, 1);
v_v_30_ = lean_ctor_get(v_x_28_, 2);
v_l_31_ = lean_ctor_get(v_x_28_, 3);
v_r_32_ = lean_ctor_get(v_x_28_, 4);
v___x_33_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0(v_init_27_, v_l_31_);
lean_inc(v_v_30_);
lean_inc(v_k_29_);
v___x_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_34_, 0, v_k_29_);
lean_ctor_set(v___x_34_, 1, v_v_30_);
v___x_35_ = lean_array_push(v___x_33_, v___x_34_);
v_init_27_ = v___x_35_;
v_x_28_ = v_r_32_;
goto _start;
}
else
{
return v_init_27_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_37_, lean_object* v_x_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0(v_init_37_, v_x_38_);
lean_dec(v_x_38_);
return v_res_39_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1(lean_object* v_env_40_, lean_object* v_as_41_, size_t v_i_42_, size_t v_stop_43_, lean_object* v_b_44_){
_start:
{
lean_object* v___y_46_; uint8_t v___x_50_; 
v___x_50_ = lean_usize_dec_eq(v_i_42_, v_stop_43_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; lean_object* v_fst_52_; uint8_t v___x_53_; lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_51_ = lean_array_uget_borrowed(v_as_41_, v_i_42_);
v_fst_52_ = lean_ctor_get(v___x_51_, 0);
v___x_53_ = 1;
lean_inc_ref(v_env_40_);
v___x_54_ = l_Lean_Environment_setExporting(v_env_40_, v___x_53_);
lean_inc(v_fst_52_);
v___x_55_ = l_Lean_Environment_contains(v___x_54_, v_fst_52_, v___x_53_);
if (v___x_55_ == 0)
{
v___y_46_ = v_b_44_;
goto v___jp_45_;
}
else
{
lean_object* v___x_56_; 
lean_inc(v___x_51_);
v___x_56_ = lean_array_push(v_b_44_, v___x_51_);
v___y_46_ = v___x_56_;
goto v___jp_45_;
}
}
else
{
lean_dec_ref(v_env_40_);
return v_b_44_;
}
v___jp_45_:
{
size_t v___x_47_; size_t v___x_48_; 
v___x_47_ = ((size_t)1ULL);
v___x_48_ = lean_usize_add(v_i_42_, v___x_47_);
v_i_42_ = v___x_48_;
v_b_44_ = v___y_46_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_40_ = stack[0].m_obj;
lean_object* v_as_41_ = stack[1].m_obj;
size_t v_i_42_ = stack[2].m_num;
size_t v_stop_43_ = stack[3].m_num;
lean_object* v_b_44_ = stack[4].m_obj;
lean_object* v_res_57_;
v_res_57_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1(v_env_40_, v_as_41_, v_i_42_, v_stop_43_, v_b_44_);
stack->m_obj
 = v_res_57_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_58_, lean_object* v_as_59_, lean_object* v_i_60_, lean_object* v_stop_61_, lean_object* v_b_62_){
_start:
{
size_t v_i_boxed_63_; size_t v_stop_boxed_64_; lean_object* v_res_65_; 
v_i_boxed_63_ = lean_unbox_usize(v_i_60_);
lean_dec(v_i_60_);
v_stop_boxed_64_ = lean_unbox_usize(v_stop_61_);
lean_dec(v_stop_61_);
v_res_65_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1(v_env_58_, v_as_59_, v_i_boxed_63_, v_stop_boxed_64_, v_b_62_);
lean_dec_ref(v_as_59_);
return v_res_65_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__2(lean_object* v_env_66_, lean_object* v_as_67_, size_t v_i_68_, size_t v_stop_69_, lean_object* v_b_70_){
_start:
{
lean_object* v___y_72_; uint8_t v___x_76_; 
v___x_76_ = lean_usize_dec_eq(v_i_68_, v_stop_69_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v_fst_78_; uint8_t v___x_79_; 
v___x_77_ = lean_array_uget_borrowed(v_as_67_, v_i_68_);
v_fst_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v_fst_78_);
lean_inc_ref(v_env_66_);
v___x_79_ = l_Lean_Environment_contains(v_env_66_, v_fst_78_, v___x_76_);
if (v___x_79_ == 0)
{
v___y_72_ = v_b_70_;
goto v___jp_71_;
}
else
{
lean_object* v___x_80_; 
lean_inc(v___x_77_);
v___x_80_ = lean_array_push(v_b_70_, v___x_77_);
v___y_72_ = v___x_80_;
goto v___jp_71_;
}
}
else
{
lean_dec_ref(v_env_66_);
return v_b_70_;
}
v___jp_71_:
{
size_t v___x_73_; size_t v___x_74_; 
v___x_73_ = ((size_t)1ULL);
v___x_74_ = lean_usize_add(v_i_68_, v___x_73_);
v_i_68_ = v___x_74_;
v_b_70_ = v___y_72_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_66_ = stack[0].m_obj;
lean_object* v_as_67_ = stack[1].m_obj;
size_t v_i_68_ = stack[2].m_num;
size_t v_stop_69_ = stack[3].m_num;
lean_object* v_b_70_ = stack[4].m_obj;
lean_object* v_res_81_;
v_res_81_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__2(v_env_66_, v_as_67_, v_i_68_, v_stop_69_, v_b_70_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_82_, lean_object* v_as_83_, lean_object* v_i_84_, lean_object* v_stop_85_, lean_object* v_b_86_){
_start:
{
size_t v_i_boxed_87_; size_t v_stop_boxed_88_; lean_object* v_res_89_; 
v_i_boxed_87_ = lean_unbox_usize(v_i_84_);
lean_dec(v_i_84_);
v_stop_boxed_88_ = lean_unbox_usize(v_stop_85_);
lean_dec(v_stop_85_);
v_res_89_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__2(v_env_82_, v_as_83_, v_i_boxed_87_, v_stop_boxed_88_, v_b_86_);
lean_dec_ref(v_as_83_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_(lean_object* v_env_94_, lean_object* v_s_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___y_98_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_96_ = lean_unsigned_to_nat(0u);
v___x_113_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_114_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0(v___x_113_, v_s_95_);
v___x_115_ = lean_array_get_size(v___x_114_);
v___x_116_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_117_ = lean_nat_dec_lt(v___x_96_, v___x_115_);
if (v___x_117_ == 0)
{
lean_dec_ref(v___x_114_);
v___y_98_ = v___x_116_;
goto v___jp_97_;
}
else
{
uint8_t v___x_118_; 
v___x_118_ = lean_nat_dec_le(v___x_115_, v___x_115_);
if (v___x_118_ == 0)
{
if (v___x_117_ == 0)
{
lean_dec_ref(v___x_114_);
v___y_98_ = v___x_116_;
goto v___jp_97_;
}
else
{
size_t v___x_119_; size_t v___x_120_; lean_object* v___x_121_; 
v___x_119_ = ((size_t)0ULL);
v___x_120_ = lean_usize_of_nat(v___x_115_);
lean_inc_ref(v_env_94_);
v___x_121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__2(v_env_94_, v___x_114_, v___x_119_, v___x_120_, v___x_116_);
lean_dec_ref(v___x_114_);
v___y_98_ = v___x_121_;
goto v___jp_97_;
}
}
else
{
size_t v___x_122_; size_t v___x_123_; lean_object* v___x_124_; 
v___x_122_ = ((size_t)0ULL);
v___x_123_ = lean_usize_of_nat(v___x_115_);
lean_inc_ref(v_env_94_);
v___x_124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__2(v_env_94_, v___x_114_, v___x_122_, v___x_123_, v___x_116_);
lean_dec_ref(v___x_114_);
v___y_98_ = v___x_124_;
goto v___jp_97_;
}
}
v___jp_97_:
{
lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_99_ = lean_array_get_size(v___y_98_);
v___x_100_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_101_ = lean_nat_dec_lt(v___x_96_, v___x_99_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; 
lean_dec_ref(v_env_94_);
v___x_102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set(v___x_102_, 1, v___x_100_);
lean_ctor_set(v___x_102_, 2, v___y_98_);
return v___x_102_;
}
else
{
uint8_t v___x_103_; 
v___x_103_ = lean_nat_dec_le(v___x_99_, v___x_99_);
if (v___x_103_ == 0)
{
if (v___x_101_ == 0)
{
lean_object* v___x_104_; 
lean_dec_ref(v_env_94_);
v___x_104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_104_, 0, v___x_100_);
lean_ctor_set(v___x_104_, 1, v___x_100_);
lean_ctor_set(v___x_104_, 2, v___y_98_);
return v___x_104_;
}
else
{
size_t v___x_105_; size_t v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_105_ = ((size_t)0ULL);
v___x_106_ = lean_usize_of_nat(v___x_99_);
v___x_107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1(v_env_94_, v___y_98_, v___x_105_, v___x_106_, v___x_100_);
lean_inc_ref(v___x_107_);
v___x_108_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
lean_ctor_set(v___x_108_, 2, v___y_98_);
return v___x_108_;
}
}
else
{
size_t v___x_109_; size_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_109_ = ((size_t)0ULL);
v___x_110_ = lean_usize_of_nat(v___x_99_);
v___x_111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1(v_env_94_, v___y_98_, v___x_109_, v___x_110_, v___x_100_);
lean_inc_ref(v___x_111_);
v___x_112_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
lean_ctor_set(v___x_112_, 2, v___y_98_);
return v___x_112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2____boxed(lean_object* v_env_125_, lean_object* v_s_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_(v_env_125_, v_s_126_);
lean_dec(v_s_126_);
return v_res_127_;
}
}
lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; lean_object* v___x_143_; 
v___f_139_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_140_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_141_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_142_ = 0;
v___x_143_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_140_, v___x_141_, v___x_142_, v___f_139_);
return v___x_143_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_144_;
v_res_144_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_();
stack->m_obj
 = v_res_144_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2____boxed(lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_();
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0(lean_object* v_init_147_, lean_object* v_t_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0(v_init_147_, v_t_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_150_, lean_object* v_t_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0(v_init_150_, v_t_151_);
lean_dec(v_t_151_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(lean_object* v_env_158_, lean_object* v_opts_159_, lean_object* v_procName_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1));
v___x_162_ = l_Lean_Environment_evalConstCheck___redArg(v_env_158_, v_opts_159_, v___x_161_, v_procName_160_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___boxed(lean_object* v_env_163_, lean_object* v_opts_164_, lean_object* v_procName_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(v_env_163_, v_opts_164_, v_procName_165_);
lean_dec_ref(v_opts_164_);
return v_res_166_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_167_, lean_object* v_i_168_, lean_object* v_k_169_){
_start:
{
lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = lean_array_get_size(v_keys_167_);
v___x_171_ = lean_nat_dec_lt(v_i_168_, v___x_170_);
if (v___x_171_ == 0)
{
lean_dec(v_i_168_);
return v___x_171_;
}
else
{
lean_object* v_k_x27_172_; uint8_t v___x_173_; 
v_k_x27_172_ = lean_array_fget_borrowed(v_keys_167_, v_i_168_);
v___x_173_ = lean_name_eq(v_k_169_, v_k_x27_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_nat_add(v_i_168_, v___x_174_);
lean_dec(v_i_168_);
v_i_168_ = v___x_175_;
goto _start;
}
else
{
lean_dec(v_i_168_);
return v___x_171_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_167_ = stack[0].m_obj;
lean_object* v_i_168_ = stack[1].m_obj;
lean_object* v_k_169_ = stack[2].m_obj;
uint8_t v_res_177_;
v_res_177_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg(v_keys_167_, v_i_168_, v_k_169_);
stack->m_num = v_res_177_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_178_, lean_object* v_i_179_, lean_object* v_k_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg(v_keys_178_, v_i_179_, v_k_180_);
lean_dec(v_k_180_);
lean_dec_ref(v_keys_178_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg(lean_object* v_x_183_, size_t v_x_184_, lean_object* v_x_185_){
_start:
{
if (lean_obj_tag(v_x_183_) == 0)
{
lean_object* v_es_186_; lean_object* v___x_187_; size_t v___x_188_; size_t v___x_189_; lean_object* v_j_190_; lean_object* v___x_191_; 
v_es_186_ = lean_ctor_get(v_x_183_, 0);
v___x_187_ = lean_box(2);
v___x_188_ = ((size_t)31ULL);
v___x_189_ = lean_usize_land(v_x_184_, v___x_188_);
v_j_190_ = lean_usize_to_nat(v___x_189_);
v___x_191_ = lean_array_get_borrowed(v___x_187_, v_es_186_, v_j_190_);
lean_dec(v_j_190_);
switch(lean_obj_tag(v___x_191_))
{
case 0:
{
lean_object* v_key_192_; uint8_t v___x_193_; 
v_key_192_ = lean_ctor_get(v___x_191_, 0);
v___x_193_ = lean_name_eq(v_x_185_, v_key_192_);
return v___x_193_;
}
case 1:
{
lean_object* v_node_194_; size_t v___x_195_; size_t v___x_196_; 
v_node_194_ = lean_ctor_get(v___x_191_, 0);
v___x_195_ = ((size_t)5ULL);
v___x_196_ = lean_usize_shift_right(v_x_184_, v___x_195_);
v_x_183_ = v_node_194_;
v_x_184_ = v___x_196_;
goto _start;
}
default: 
{
uint8_t v___x_198_; 
v___x_198_ = 0;
return v___x_198_;
}
}
}
else
{
lean_object* v_ks_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v_ks_199_ = lean_ctor_get(v_x_183_, 0);
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg(v_ks_199_, v___x_200_, v_x_185_);
return v___x_201_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_183_ = stack[0].m_obj;
size_t v_x_184_ = stack[1].m_num;
lean_object* v_x_185_ = stack[2].m_obj;
uint8_t v_res_202_;
v_res_202_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg(v_x_183_, v_x_184_, v_x_185_);
stack->m_num = v_res_202_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___boxed(lean_object* v_x_203_, lean_object* v_x_204_, lean_object* v_x_205_){
_start:
{
size_t v_x_242__boxed_206_; uint8_t v_res_207_; lean_object* v_r_208_; 
v_x_242__boxed_206_ = lean_unbox_usize(v_x_204_);
lean_dec(v_x_204_);
v_res_207_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg(v_x_203_, v_x_242__boxed_206_, v_x_205_);
lean_dec(v_x_205_);
lean_dec_ref(v_x_203_);
v_r_208_ = lean_box(v_res_207_);
return v_r_208_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
uint64_t v___y_212_; 
if (lean_obj_tag(v_x_210_) == 0)
{
uint64_t v___x_215_; 
v___x_215_ = 1723ULL;
v___y_212_ = v___x_215_;
goto v___jp_211_;
}
else
{
uint64_t v_hash_216_; 
v_hash_216_ = lean_ctor_get_uint64(v_x_210_, sizeof(void*)*2);
v___y_212_ = v_hash_216_;
goto v___jp_211_;
}
v___jp_211_:
{
size_t v___x_213_; uint8_t v___x_214_; 
v___x_213_ = lean_uint64_to_usize(v___y_212_);
v___x_214_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg(v_x_209_, v___x_213_, v_x_210_);
return v___x_214_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_209_ = stack[0].m_obj;
lean_object* v_x_210_ = stack[1].m_obj;
uint8_t v_res_217_;
v_res_217_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(v_x_209_, v_x_210_);
stack->m_num = v_res_217_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___boxed(lean_object* v_x_218_, lean_object* v_x_219_){
_start:
{
uint8_t v_res_220_; lean_object* v_r_221_; 
v_res_220_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(v_x_218_, v_x_219_);
lean_dec(v_x_219_);
lean_dec_ref(v_x_218_);
v_r_221_ = lean_box(v_res_220_);
return v_r_221_;
}
}
lean_object* l_Lean_Server_existsBuiltinRpcProcedure(lean_object* v_method_222_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_224_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_225_ = lean_st_ref_get(v___x_224_);
v___x_226_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(v___x_225_, v_method_222_);
lean_dec(v___x_225_);
v___x_227_ = lean_box(v___x_226_);
v___x_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT void l_Lean_Server_existsBuiltinRpcProcedure_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_222_ = stack[0].m_obj;
lean_object* v_res_229_;
v_res_229_ = l_Lean_Server_existsBuiltinRpcProcedure(v_method_222_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l_Lean_Server_existsBuiltinRpcProcedure___boxed(lean_object* v_method_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Server_existsBuiltinRpcProcedure(v_method_230_);
lean_dec(v_method_230_);
return v_res_232_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0(lean_object* v_00_u03b2_233_, lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
uint8_t v___x_236_; 
v___x_236_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(v_x_234_, v_x_235_);
return v___x_236_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_234_ = stack[1].m_obj;
lean_object* v_x_235_ = stack[2].m_obj;
uint8_t v_res_237_;
v_res_237_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0(lean_box(0), v_x_234_, v_x_235_);
stack->m_num = v_res_237_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___boxed(lean_object* v_00_u03b2_238_, lean_object* v_x_239_, lean_object* v_x_240_){
_start:
{
uint8_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0(v_00_u03b2_238_, v_x_239_, v_x_240_);
lean_dec(v_x_240_);
lean_dec_ref(v_x_239_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0(lean_object* v_00_u03b2_243_, lean_object* v_x_244_, size_t v_x_245_, lean_object* v_x_246_){
_start:
{
uint8_t v___x_247_; 
v___x_247_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg(v_x_244_, v_x_245_, v_x_246_);
return v___x_247_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_244_ = stack[1].m_obj;
size_t v_x_245_ = stack[2].m_num;
lean_object* v_x_246_ = stack[3].m_obj;
uint8_t v_res_248_;
v_res_248_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0(lean_box(0), v_x_244_, v_x_245_, v_x_246_);
stack->m_num = v_res_248_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___boxed(lean_object* v_00_u03b2_249_, lean_object* v_x_250_, lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
size_t v_x_362__boxed_253_; uint8_t v_res_254_; lean_object* v_r_255_; 
v_x_362__boxed_253_ = lean_unbox_usize(v_x_251_);
lean_dec(v_x_251_);
v_res_254_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0(v_00_u03b2_249_, v_x_250_, v_x_362__boxed_253_, v_x_252_);
lean_dec(v_x_252_);
lean_dec_ref(v_x_250_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_256_, lean_object* v_keys_257_, lean_object* v_vals_258_, lean_object* v_heq_259_, lean_object* v_i_260_, lean_object* v_k_261_){
_start:
{
uint8_t v___x_262_; 
v___x_262_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg(v_keys_257_, v_i_260_, v_k_261_);
return v___x_262_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_257_ = stack[1].m_obj;
lean_object* v_vals_258_ = stack[2].m_obj;
lean_object* v_i_260_ = stack[4].m_obj;
lean_object* v_k_261_ = stack[5].m_obj;
uint8_t v_res_263_;
v_res_263_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1(lean_box(0), v_keys_257_, v_vals_258_, lean_box(0), v_i_260_, v_k_261_);
stack->m_num = v_res_263_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_264_, lean_object* v_keys_265_, lean_object* v_vals_266_, lean_object* v_heq_267_, lean_object* v_i_268_, lean_object* v_k_269_){
_start:
{
uint8_t v_res_270_; lean_object* v_r_271_; 
v_res_270_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1(v_00_u03b2_264_, v_keys_265_, v_vals_266_, v_heq_267_, v_i_268_, v_k_269_);
lean_dec(v_k_269_);
lean_dec_ref(v_vals_266_);
lean_dec_ref(v_keys_265_);
v_r_271_ = lean_box(v_res_270_);
return v_r_271_;
}
}
lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1(lean_object* v___y_272_){
_start:
{
lean_object* v_doc_274_; lean_object* v___x_275_; 
v_doc_274_ = lean_ctor_get(v___y_272_, 1);
lean_inc_ref(v_doc_274_);
v___x_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_275_, 0, v_doc_274_);
return v___x_275_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_272_ = stack[0].m_obj;
lean_object* v_res_276_;
v_res_276_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1(v___y_272_);
stack->m_obj
 = v_res_276_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1___boxed(lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1(v___y_277_);
lean_dec_ref(v___y_277_);
return v_res_279_;
}
}
lean_object* l_Lean_Server_handleRpcCall___lam__0(lean_object* v_val_280_, uint64_t v_sessionId_281_, lean_object* v_params_282_, lean_object* v___y_283_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_box_uint64(v_sessionId_281_);
lean_inc_ref(v___y_283_);
v___x_286_ = lean_apply_4(v_val_280_, v___x_285_, v_params_282_, v___y_283_, lean_box(0));
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_300_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_300_ == 0)
{
v___x_289_ = v___x_286_;
v_isShared_290_ = v_isSharedCheck_300_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_300_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; 
v___x_291_ = lean_io_wait(v_a_287_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_294_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_a_292_);
lean_dec_ref_known(v___x_291_, 1);
if (v_isShared_290_ == 0)
{
lean_ctor_set_tag(v___x_289_, 1);
lean_ctor_set(v___x_289_, 0, v_a_292_);
v___x_294_ = v___x_289_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; 
v_a_296_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_a_296_);
lean_dec_ref_known(v___x_291_, 1);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v_a_296_);
v___x_298_ = v___x_289_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
else
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
v_a_301_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_286_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_286_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_handleRpcCall___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_280_ = stack[0].m_obj;
uint64_t v_sessionId_281_ = stack[1].m_num;
lean_object* v_params_282_ = stack[2].m_obj;
lean_object* v___y_283_ = stack[3].m_obj;
lean_object* v_res_309_;
v_res_309_ = l_Lean_Server_handleRpcCall___lam__0(v_val_280_, v_sessionId_281_, v_params_282_, v___y_283_);
stack->m_obj
 = v_res_309_;
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__0___boxed(lean_object* v_val_310_, lean_object* v_sessionId_311_, lean_object* v_params_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
uint64_t v_sessionId_boxed_315_; lean_object* v_res_316_; 
v_sessionId_boxed_315_ = lean_unbox_uint64(v_sessionId_311_);
lean_dec_ref(v_sessionId_311_);
v_res_316_ = l_Lean_Server_handleRpcCall___lam__0(v_val_310_, v_sessionId_boxed_315_, v_params_312_, v___y_313_);
lean_dec_ref(v___y_313_);
return v_res_316_;
}
}
uint8_t l_Lean_Server_handleRpcCall___lam__1(lean_object* v___x_317_, lean_object* v___x_318_, lean_object* v_method_319_, lean_object* v_s_320_){
_start:
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_320_);
v___x_322_ = lean_nat_dec_le(v___x_317_, v___x_321_);
lean_dec(v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v_toEnvExtension_324_; lean_object* v_asyncMode_325_; lean_object* v___x_326_; uint8_t v___x_327_; lean_object* v___x_328_; 
v___x_323_ = l_Lean_Server_userRpcProcedures;
v_toEnvExtension_324_ = lean_ctor_get(v___x_323_, 0);
v_asyncMode_325_ = lean_ctor_get(v_toEnvExtension_324_, 2);
v___x_326_ = l_Lean_Server_Snapshots_Snapshot_env(v_s_320_);
v___x_327_ = 0;
v___x_328_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_318_, v___x_323_, v___x_326_, v_method_319_, v_asyncMode_325_, v___x_327_);
if (lean_obj_tag(v___x_328_) == 0)
{
return v___x_322_;
}
else
{
uint8_t v___x_329_; 
lean_dec_ref_known(v___x_328_, 1);
v___x_329_ = 1;
return v___x_329_;
}
}
else
{
lean_dec(v_method_319_);
lean_dec(v___x_318_);
return v___x_322_;
}
}
}
LEAN_EXPORT void l_Lean_Server_handleRpcCall___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_317_ = stack[0].m_obj;
lean_object* v___x_318_ = stack[1].m_obj;
lean_object* v_method_319_ = stack[2].m_obj;
lean_object* v_s_320_ = stack[3].m_obj;
uint8_t v_res_330_;
v_res_330_ = l_Lean_Server_handleRpcCall___lam__1(v___x_317_, v___x_318_, v_method_319_, v_s_320_);
stack->m_num = v_res_330_;
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__1___boxed(lean_object* v___x_331_, lean_object* v___x_332_, lean_object* v_method_333_, lean_object* v_s_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_Lean_Server_handleRpcCall___lam__1(v___x_331_, v___x_332_, v_method_333_, v_s_334_);
lean_dec_ref(v_s_334_);
lean_dec(v___x_331_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
lean_object* l_Lean_Server_handleRpcCall___lam__2(lean_object* v___x_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_337_);
return v___x_340_;
}
}
LEAN_EXPORT void l_Lean_Server_handleRpcCall___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_337_ = stack[0].m_obj;
lean_object* v___y_338_ = stack[1].m_obj;
lean_object* v_res_341_;
v_res_341_ = l_Lean_Server_handleRpcCall___lam__2(v___x_337_, v___y_338_);
stack->m_obj
 = v_res_341_;
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__2___boxed(lean_object* v___x_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Server_handleRpcCall___lam__2(v___x_342_, v___y_343_);
lean_dec_ref(v___y_343_);
return v_res_345_;
}
}
lean_object* l_Lean_Server_handleRpcCall___lam__3(lean_object* v___x_348_, lean_object* v_method_349_, lean_object* v___x_350_, uint8_t v___x_351_, uint64_t v_sessionId_352_, lean_object* v_params_353_, lean_object* v___x_354_, lean_object* v_snap_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; lean_object* v_toEnvExtension_359_; lean_object* v_asyncMode_360_; lean_object* v___x_361_; uint8_t v___x_362_; lean_object* v___x_363_; 
v___x_358_ = l_Lean_Server_userRpcProcedures;
v_toEnvExtension_359_ = lean_ctor_get(v___x_358_, 0);
v_asyncMode_360_ = lean_ctor_get(v_toEnvExtension_359_, 2);
v___x_361_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_355_);
v___x_362_ = 0;
lean_inc_ref(v___x_361_);
v___x_363_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_348_, v___x_358_, v___x_361_, v_method_349_, v_asyncMode_360_, v___x_362_);
if (lean_obj_tag(v___x_363_) == 1)
{
lean_object* v_cmdState_364_; lean_object* v_val_365_; lean_object* v_scopes_366_; lean_object* v___x_367_; lean_object* v_opts_368_; lean_object* v___x_369_; 
lean_dec_ref(v___x_354_);
v_cmdState_364_ = lean_ctor_get(v_snap_355_, 2);
v_val_365_ = lean_ctor_get(v___x_363_, 0);
lean_inc_n(v_val_365_, 2);
lean_dec_ref_known(v___x_363_, 1);
v_scopes_366_ = lean_ctor_get(v_cmdState_364_, 2);
v___x_367_ = l_List_head_x21___redArg(v___x_350_, v_scopes_366_);
v_opts_368_ = lean_ctor_get(v___x_367_, 1);
lean_inc_ref(v_opts_368_);
lean_dec(v___x_367_);
v___x_369_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(v___x_361_, v_opts_368_, v_val_365_);
lean_dec_ref(v_opts_368_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_385_; 
lean_dec(v_params_353_);
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_385_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_385_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_385_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_374_ = 4;
v___x_375_ = ((lean_object*)(l_Lean_Server_handleRpcCall___lam__3___closed__0));
v___x_376_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_365_, v___x_351_);
v___x_377_ = lean_string_append(v___x_375_, v___x_376_);
lean_dec_ref(v___x_376_);
v___x_378_ = ((lean_object*)(l_Lean_Server_handleRpcCall___lam__3___closed__1));
v___x_379_ = lean_string_append(v___x_377_, v___x_378_);
v___x_380_ = lean_string_append(v___x_379_, v_a_370_);
lean_dec(v_a_370_);
v___x_381_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*1, v___x_374_);
if (v_isShared_373_ == 0)
{
lean_ctor_set_tag(v___x_372_, 1);
lean_ctor_set(v___x_372_, 0, v___x_381_);
v___x_383_ = v___x_372_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
else
{
lean_object* v_a_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
lean_dec(v_val_365_);
v_a_386_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_369_, 1);
v___x_387_ = lean_box_uint64(v_sessionId_352_);
lean_inc_ref(v___y_356_);
v___x_388_ = lean_apply_4(v_a_386_, v___x_387_, v_params_353_, v___y_356_, lean_box(0));
return v___x_388_;
}
}
else
{
lean_object* v___x_389_; 
lean_dec(v___x_363_);
lean_dec_ref(v___x_361_);
lean_dec(v_params_353_);
v___x_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_354_);
return v___x_389_;
}
}
}
LEAN_EXPORT void l_Lean_Server_handleRpcCall___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_348_ = stack[0].m_obj;
lean_object* v_method_349_ = stack[1].m_obj;
lean_object* v___x_350_ = stack[2].m_obj;
uint8_t v___x_351_ = stack[3].m_num;
uint64_t v_sessionId_352_ = stack[4].m_num;
lean_object* v_params_353_ = stack[5].m_obj;
lean_object* v___x_354_ = stack[6].m_obj;
lean_object* v_snap_355_ = stack[7].m_obj;
lean_object* v___y_356_ = stack[8].m_obj;
lean_object* v_res_390_;
v_res_390_ = l_Lean_Server_handleRpcCall___lam__3(v___x_348_, v_method_349_, v___x_350_, v___x_351_, v_sessionId_352_, v_params_353_, v___x_354_, v_snap_355_, v___y_356_);
stack->m_obj
 = v_res_390_;
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__3___boxed(lean_object* v___x_391_, lean_object* v_method_392_, lean_object* v___x_393_, lean_object* v___x_394_, lean_object* v_sessionId_395_, lean_object* v_params_396_, lean_object* v___x_397_, lean_object* v_snap_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
uint8_t v___x_2375__boxed_401_; uint64_t v_sessionId_boxed_402_; lean_object* v_res_403_; 
v___x_2375__boxed_401_ = lean_unbox(v___x_394_);
v_sessionId_boxed_402_ = lean_unbox_uint64(v_sessionId_395_);
lean_dec_ref(v_sessionId_395_);
v_res_403_ = l_Lean_Server_handleRpcCall___lam__3(v___x_391_, v_method_392_, v___x_393_, v___x_2375__boxed_401_, v_sessionId_boxed_402_, v_params_396_, v___x_397_, v_snap_398_, v___y_399_);
lean_dec_ref(v___y_399_);
lean_dec_ref(v_snap_398_);
lean_dec_ref(v___x_393_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_404_, lean_object* v_vals_405_, lean_object* v_i_406_, lean_object* v_k_407_){
_start:
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = lean_array_get_size(v_keys_404_);
v___x_409_ = lean_nat_dec_lt(v_i_406_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; 
lean_dec(v_i_406_);
v___x_410_ = lean_box(0);
return v___x_410_;
}
else
{
lean_object* v_k_x27_411_; uint8_t v___x_412_; 
v_k_x27_411_ = lean_array_fget_borrowed(v_keys_404_, v_i_406_);
v___x_412_ = lean_name_eq(v_k_407_, v_k_x27_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_unsigned_to_nat(1u);
v___x_414_ = lean_nat_add(v_i_406_, v___x_413_);
lean_dec(v_i_406_);
v_i_406_ = v___x_414_;
goto _start;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_array_fget_borrowed(v_vals_405_, v_i_406_);
lean_dec(v_i_406_);
lean_inc(v___x_416_);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
return v___x_417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_418_, lean_object* v_vals_419_, lean_object* v_i_420_, lean_object* v_k_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(v_keys_418_, v_vals_419_, v_i_420_, v_k_421_);
lean_dec(v_k_421_);
lean_dec_ref(v_vals_419_);
lean_dec_ref(v_keys_418_);
return v_res_422_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(lean_object* v_x_423_, size_t v_x_424_, lean_object* v_x_425_){
_start:
{
if (lean_obj_tag(v_x_423_) == 0)
{
lean_object* v_es_426_; lean_object* v___x_427_; size_t v___x_428_; size_t v___x_429_; lean_object* v_j_430_; lean_object* v___x_431_; 
v_es_426_ = lean_ctor_get(v_x_423_, 0);
v___x_427_ = lean_box(2);
v___x_428_ = ((size_t)31ULL);
v___x_429_ = lean_usize_land(v_x_424_, v___x_428_);
v_j_430_ = lean_usize_to_nat(v___x_429_);
v___x_431_ = lean_array_get_borrowed(v___x_427_, v_es_426_, v_j_430_);
lean_dec(v_j_430_);
switch(lean_obj_tag(v___x_431_))
{
case 0:
{
lean_object* v_key_432_; lean_object* v_val_433_; uint8_t v___x_434_; 
v_key_432_ = lean_ctor_get(v___x_431_, 0);
v_val_433_ = lean_ctor_get(v___x_431_, 1);
v___x_434_ = lean_name_eq(v_x_425_, v_key_432_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
v___x_435_ = lean_box(0);
return v___x_435_;
}
else
{
lean_object* v___x_436_; 
lean_inc(v_val_433_);
v___x_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_436_, 0, v_val_433_);
return v___x_436_;
}
}
case 1:
{
lean_object* v_node_437_; size_t v___x_438_; size_t v___x_439_; 
v_node_437_ = lean_ctor_get(v___x_431_, 0);
v___x_438_ = ((size_t)5ULL);
v___x_439_ = lean_usize_shift_right(v_x_424_, v___x_438_);
v_x_423_ = v_node_437_;
v_x_424_ = v___x_439_;
goto _start;
}
default: 
{
lean_object* v___x_441_; 
v___x_441_ = lean_box(0);
return v___x_441_;
}
}
}
else
{
lean_object* v_ks_442_; lean_object* v_vs_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_ks_442_ = lean_ctor_get(v_x_423_, 0);
v_vs_443_ = lean_ctor_get(v_x_423_, 1);
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(v_ks_442_, v_vs_443_, v___x_444_, v_x_425_);
return v___x_445_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_423_ = stack[0].m_obj;
size_t v_x_424_ = stack[1].m_num;
lean_object* v_x_425_ = stack[2].m_obj;
lean_object* v_res_446_;
v_res_446_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(v_x_423_, v_x_424_, v_x_425_);
stack->m_obj
 = v_res_446_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg___boxed(lean_object* v_x_447_, lean_object* v_x_448_, lean_object* v_x_449_){
_start:
{
size_t v_x_2516__boxed_450_; lean_object* v_res_451_; 
v_x_2516__boxed_450_ = lean_unbox_usize(v_x_448_);
lean_dec(v_x_448_);
v_res_451_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(v_x_447_, v_x_2516__boxed_450_, v_x_449_);
lean_dec(v_x_449_);
lean_dec_ref(v_x_447_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
uint64_t v___y_455_; 
if (lean_obj_tag(v_x_453_) == 0)
{
uint64_t v___x_458_; 
v___x_458_ = 1723ULL;
v___y_455_ = v___x_458_;
goto v___jp_454_;
}
else
{
uint64_t v_hash_459_; 
v_hash_459_ = lean_ctor_get_uint64(v_x_453_, sizeof(void*)*2);
v___y_455_ = v_hash_459_;
goto v___jp_454_;
}
v___jp_454_:
{
size_t v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_uint64_to_usize(v___y_455_);
v___x_457_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(v_x_452_, v___x_456_, v_x_453_);
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg___boxed(lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(v_x_460_, v_x_461_);
lean_dec(v_x_461_);
lean_dec_ref(v_x_460_);
return v_res_462_;
}
}
lean_object* l_Lean_Server_handleRpcCall(lean_object* v_p_465_, lean_object* v_a_466_){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v_toTextDocumentPositionParams_472_; uint64_t v_sessionId_473_; lean_object* v_method_474_; lean_object* v_params_475_; lean_object* v___x_476_; 
v___x_468_ = lean_box(0);
v___x_469_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_470_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_471_ = lean_st_ref_get(v___x_470_);
v_toTextDocumentPositionParams_472_ = lean_ctor_get(v_p_465_, 0);
lean_inc_ref(v_toTextDocumentPositionParams_472_);
v_sessionId_473_ = lean_ctor_get_uint64(v_p_465_, sizeof(void*)*3);
v_method_474_ = lean_ctor_get(v_p_465_, 1);
lean_inc(v_method_474_);
v_params_475_ = lean_ctor_get(v_p_465_, 2);
lean_inc(v_params_475_);
lean_dec_ref(v_p_465_);
v___x_476_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(v___x_471_, v_method_474_);
lean_dec(v___x_471_);
if (lean_obj_tag(v___x_476_) == 1)
{
lean_object* v_val_477_; lean_object* v___x_478_; lean_object* v___f_479_; lean_object* v___x_480_; 
lean_dec(v_method_474_);
lean_dec_ref(v_toTextDocumentPositionParams_472_);
v_val_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_val_477_);
lean_dec_ref_known(v___x_476_, 1);
v___x_478_ = lean_box_uint64(v_sessionId_473_);
v___f_479_ = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__0___boxed), 5, 3);
lean_closure_set(v___f_479_, 0, v_val_477_);
lean_closure_set(v___f_479_, 1, v___x_478_);
lean_closure_set(v___f_479_, 2, v_params_475_);
v___x_480_ = l_Lean_Server_RequestM_asTask___redArg(v___f_479_, v_a_466_);
return v___x_480_;
}
else
{
lean_object* v___x_481_; lean_object* v_a_482_; lean_object* v_toEditableDocumentCore_483_; lean_object* v_meta_484_; lean_object* v_text_485_; lean_object* v_position_486_; lean_object* v___x_487_; lean_object* v___f_488_; uint8_t v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___f_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___f_500_; lean_object* v___x_501_; 
lean_dec(v___x_476_);
v___x_481_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1(v_a_466_);
v_a_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_a_482_);
lean_dec_ref(v___x_481_);
v_toEditableDocumentCore_483_ = lean_ctor_get(v_a_482_, 0);
v_meta_484_ = lean_ctor_get(v_toEditableDocumentCore_483_, 0);
v_text_485_ = lean_ctor_get(v_meta_484_, 3);
v_position_486_ = lean_ctor_get(v_toTextDocumentPositionParams_472_, 1);
lean_inc_ref(v_position_486_);
lean_dec_ref(v_toTextDocumentPositionParams_472_);
v___x_487_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_485_, v_position_486_);
lean_inc_n(v_method_474_, 2);
v___f_488_ = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__1___boxed), 4, 3);
lean_closure_set(v___f_488_, 0, v___x_487_);
lean_closure_set(v___f_488_, 1, v___x_468_);
lean_closure_set(v___f_488_, 2, v_method_474_);
v___x_489_ = 2;
v___x_490_ = ((lean_object*)(l_Lean_Server_handleRpcCall___closed__0));
v___x_491_ = 1;
v___x_492_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_474_, v___x_491_);
v___x_493_ = lean_string_append(v___x_490_, v___x_492_);
lean_dec_ref(v___x_492_);
v___x_494_ = ((lean_object*)(l_Lean_Server_handleRpcCall___closed__1));
v___x_495_ = lean_string_append(v___x_493_, v___x_494_);
v___x_496_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_496_, 0, v___x_495_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*1, v___x_489_);
lean_inc_ref(v___x_496_);
v___f_497_ = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__2___boxed), 3, 1);
lean_closure_set(v___f_497_, 0, v___x_496_);
v___x_498_ = lean_box(v___x_491_);
v___x_499_ = lean_box_uint64(v_sessionId_473_);
v___f_500_ = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__3___boxed), 10, 7);
lean_closure_set(v___f_500_, 0, v___x_468_);
lean_closure_set(v___f_500_, 1, v_method_474_);
lean_closure_set(v___f_500_, 2, v___x_469_);
lean_closure_set(v___f_500_, 3, v___x_498_);
lean_closure_set(v___f_500_, 4, v___x_499_);
lean_closure_set(v___f_500_, 5, v_params_475_);
lean_closure_set(v___f_500_, 6, v___x_496_);
v___x_501_ = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(v_a_482_, v___f_488_, v___f_497_, v___f_500_, v_a_466_);
return v___x_501_;
}
}
}
LEAN_EXPORT void l_Lean_Server_handleRpcCall_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_465_ = stack[0].m_obj;
lean_object* v_a_466_ = stack[1].m_obj;
lean_object* v_res_502_;
v_res_502_ = l_Lean_Server_handleRpcCall(v_p_465_, v_a_466_);
stack->m_obj
 = v_res_502_;
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___boxed(lean_object* v_p_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Server_handleRpcCall(v_p_503_, v_a_504_);
lean_dec_ref(v_a_504_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0(lean_object* v_00_u03b2_507_, lean_object* v_x_508_, lean_object* v_x_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(v_x_508_, v_x_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___boxed(lean_object* v_00_u03b2_511_, lean_object* v_x_512_, lean_object* v_x_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0(v_00_u03b2_511_, v_x_512_, v_x_513_);
lean_dec(v_x_513_);
lean_dec_ref(v_x_512_);
return v_res_514_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0(lean_object* v_00_u03b2_515_, lean_object* v_x_516_, size_t v_x_517_, lean_object* v_x_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(v_x_516_, v_x_517_, v_x_518_);
return v___x_519_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_516_ = stack[1].m_obj;
size_t v_x_517_ = stack[2].m_num;
lean_object* v_x_518_ = stack[3].m_obj;
lean_object* v_res_520_;
v_res_520_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0(lean_box(0), v_x_516_, v_x_517_, v_x_518_);
stack->m_obj
 = v_res_520_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___boxed(lean_object* v_00_u03b2_521_, lean_object* v_x_522_, lean_object* v_x_523_, lean_object* v_x_524_){
_start:
{
size_t v_x_2718__boxed_525_; lean_object* v_res_526_; 
v_x_2718__boxed_525_ = lean_unbox_usize(v_x_523_);
lean_dec(v_x_523_);
v_res_526_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0(v_00_u03b2_521_, v_x_522_, v_x_2718__boxed_525_, v_x_524_);
lean_dec(v_x_524_);
lean_dec_ref(v_x_522_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_527_, lean_object* v_keys_528_, lean_object* v_vals_529_, lean_object* v_heq_530_, lean_object* v_i_531_, lean_object* v_k_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(v_keys_528_, v_vals_529_, v_i_531_, v_k_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_534_, lean_object* v_keys_535_, lean_object* v_vals_536_, lean_object* v_heq_537_, lean_object* v_i_538_, lean_object* v_k_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2(v_00_u03b2_534_, v_keys_535_, v_vals_536_, v_heq_537_, v_i_538_, v_k_539_);
lean_dec(v_k_539_);
lean_dec_ref(v_vals_536_);
lean_dec_ref(v_keys_535_);
return v_res_540_;
}
}
lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_541_, uint8_t v_val_542_, lean_object* v___y_543_){
_start:
{
if (lean_obj_tag(v___y_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_dec(v_serialize_x3f_541_);
v_a_544_ = lean_ctor_get(v___y_543_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___y_543_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___y_543_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___y_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
else
{
if (lean_obj_tag(v_serialize_x3f_541_) == 1)
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_563_; 
v_a_552_ = lean_ctor_get(v___y_543_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___y_543_);
if (v_isSharedCheck_563_ == 0)
{
v___x_554_ = v___y_543_;
v_isShared_555_ = v_isSharedCheck_563_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___y_543_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_563_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v_val_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
v_val_556_ = lean_ctor_get(v_serialize_x3f_541_, 0);
lean_inc(v_val_556_);
lean_dec_ref_known(v_serialize_x3f_541_, 1);
v___x_557_ = lean_box(0);
v___x_558_ = lean_apply_1(v_val_556_, v_a_552_);
v___x_559_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
lean_ctor_set_uint8(v___x_559_, sizeof(void*)*2, v_val_542_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_559_);
v___x_561_ = v___x_554_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_574_; 
lean_dec(v_serialize_x3f_541_);
v_a_564_ = lean_ctor_get(v___y_543_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___y_543_);
if (v_isSharedCheck_574_ == 0)
{
v___x_566_ = v___y_543_;
v_isShared_567_ = v_isSharedCheck_574_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___y_543_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_574_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
lean_inc(v_a_564_);
v___x_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_568_, 0, v_a_564_);
v___x_569_ = l_Lean_Json_compress(v_a_564_);
v___x_570_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_570_, 0, v___x_568_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
lean_ctor_set_uint8(v___x_570_, sizeof(void*)*2, v_val_542_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_570_);
v___x_572_ = v___x_566_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_570_);
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
LEAN_EXPORT void l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_serialize_x3f_541_ = stack[0].m_obj;
uint8_t v_val_542_ = stack[1].m_num;
lean_object* v___y_543_ = stack[2].m_obj;
lean_object* v_res_575_;
v_res_575_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_541_, v_val_542_, v___y_543_);
stack->m_obj
 = v_res_575_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_576_, lean_object* v_val_577_, lean_object* v___y_578_){
_start:
{
uint8_t v_val_686__boxed_579_; lean_object* v_res_580_; 
v_val_686__boxed_579_ = lean_unbox(v_val_577_);
v_res_580_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_576_, v_val_686__boxed_579_, v___y_578_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8___redArg(lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v_x_584_){
_start:
{
lean_object* v_ks_585_; lean_object* v_vs_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_610_; 
v_ks_585_ = lean_ctor_get(v_x_581_, 0);
v_vs_586_ = lean_ctor_get(v_x_581_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_x_581_);
if (v_isSharedCheck_610_ == 0)
{
v___x_588_ = v_x_581_;
v_isShared_589_ = v_isSharedCheck_610_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_vs_586_);
lean_inc(v_ks_585_);
lean_dec(v_x_581_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_610_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = lean_array_get_size(v_ks_585_);
v___x_591_ = lean_nat_dec_lt(v_x_582_, v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_595_; 
lean_dec(v_x_582_);
v___x_592_ = lean_array_push(v_ks_585_, v_x_583_);
v___x_593_ = lean_array_push(v_vs_586_, v_x_584_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 1, v___x_593_);
lean_ctor_set(v___x_588_, 0, v___x_592_);
v___x_595_ = v___x_588_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v___x_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
else
{
lean_object* v_k_x27_597_; uint8_t v___x_598_; 
v_k_x27_597_ = lean_array_fget_borrowed(v_ks_585_, v_x_582_);
v___x_598_ = lean_string_dec_eq(v_x_583_, v_k_x27_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_600_; 
if (v_isShared_589_ == 0)
{
v___x_600_ = v___x_588_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_ks_585_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_vs_586_);
v___x_600_ = v_reuseFailAlloc_604_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_unsigned_to_nat(1u);
v___x_602_ = lean_nat_add(v_x_582_, v___x_601_);
lean_dec(v_x_582_);
v_x_581_ = v___x_600_;
v_x_582_ = v___x_602_;
goto _start;
}
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_605_ = lean_array_fset(v_ks_585_, v_x_582_, v_x_583_);
v___x_606_ = lean_array_fset(v_vs_586_, v_x_582_, v_x_584_);
lean_dec(v_x_582_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 1, v___x_606_);
lean_ctor_set(v___x_588_, 0, v___x_605_);
v___x_608_ = v___x_588_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7___redArg(lean_object* v_n_611_, lean_object* v_k_612_, lean_object* v_v_613_){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_unsigned_to_nat(0u);
v___x_615_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8___redArg(v_n_611_, v___x_614_, v_k_612_, v_v_613_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_616_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* v_x_617_, size_t v_x_618_, size_t v_x_619_, lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
if (lean_obj_tag(v_x_617_) == 0)
{
lean_object* v_es_622_; size_t v___x_623_; size_t v___x_624_; lean_object* v_j_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v_es_622_ = lean_ctor_get(v_x_617_, 0);
v___x_623_ = ((size_t)31ULL);
v___x_624_ = lean_usize_land(v_x_618_, v___x_623_);
v_j_625_ = lean_usize_to_nat(v___x_624_);
v___x_626_ = lean_array_get_size(v_es_622_);
v___x_627_ = lean_nat_dec_lt(v_j_625_, v___x_626_);
if (v___x_627_ == 0)
{
lean_dec(v_j_625_);
lean_dec(v_x_621_);
lean_dec_ref(v_x_620_);
return v_x_617_;
}
else
{
lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_666_; 
lean_inc_ref(v_es_622_);
v_isSharedCheck_666_ = !lean_is_exclusive(v_x_617_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; 
v_unused_667_ = lean_ctor_get(v_x_617_, 0);
lean_dec(v_unused_667_);
v___x_629_ = v_x_617_;
v_isShared_630_ = v_isSharedCheck_666_;
goto v_resetjp_628_;
}
else
{
lean_dec(v_x_617_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_666_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v_v_631_; lean_object* v___x_632_; lean_object* v_xs_x27_633_; lean_object* v___y_635_; 
v_v_631_ = lean_array_fget(v_es_622_, v_j_625_);
v___x_632_ = lean_box(0);
v_xs_x27_633_ = lean_array_fset(v_es_622_, v_j_625_, v___x_632_);
switch(lean_obj_tag(v_v_631_))
{
case 0:
{
lean_object* v_key_640_; lean_object* v_val_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_651_; 
v_key_640_ = lean_ctor_get(v_v_631_, 0);
v_val_641_ = lean_ctor_get(v_v_631_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_v_631_);
if (v_isSharedCheck_651_ == 0)
{
v___x_643_ = v_v_631_;
v_isShared_644_ = v_isSharedCheck_651_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_val_641_);
lean_inc(v_key_640_);
lean_dec(v_v_631_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_651_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
uint8_t v___x_645_; 
v___x_645_ = lean_string_dec_eq(v_x_620_, v_key_640_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; 
lean_del_object(v___x_643_);
v___x_646_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_640_, v_val_641_, v_x_620_, v_x_621_);
v___x_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
v___y_635_ = v___x_647_;
goto v___jp_634_;
}
else
{
lean_object* v___x_649_; 
lean_dec(v_val_641_);
lean_dec(v_key_640_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 1, v_x_621_);
lean_ctor_set(v___x_643_, 0, v_x_620_);
v___x_649_ = v___x_643_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_x_620_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_x_621_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
v___y_635_ = v___x_649_;
goto v___jp_634_;
}
}
}
}
case 1:
{
lean_object* v_node_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_664_; 
v_node_652_ = lean_ctor_get(v_v_631_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v_v_631_);
if (v_isSharedCheck_664_ == 0)
{
v___x_654_ = v_v_631_;
v_isShared_655_ = v_isSharedCheck_664_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_node_652_);
lean_dec(v_v_631_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_664_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
size_t v___x_656_; size_t v___x_657_; size_t v___x_658_; size_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_656_ = ((size_t)5ULL);
v___x_657_ = lean_usize_shift_right(v_x_618_, v___x_656_);
v___x_658_ = ((size_t)1ULL);
v___x_659_ = lean_usize_add(v_x_619_, v___x_658_);
v___x_660_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_node_652_, v___x_657_, v___x_659_, v_x_620_, v_x_621_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_660_);
v___x_662_ = v___x_654_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
v___y_635_ = v___x_662_;
goto v___jp_634_;
}
}
}
default: 
{
lean_object* v___x_665_; 
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v_x_620_);
lean_ctor_set(v___x_665_, 1, v_x_621_);
v___y_635_ = v___x_665_;
goto v___jp_634_;
}
}
v___jp_634_:
{
lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_636_ = lean_array_fset(v_xs_x27_633_, v_j_625_, v___y_635_);
lean_dec(v_j_625_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v___x_636_);
v___x_638_ = v___x_629_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
}
else
{
lean_object* v_ks_668_; lean_object* v_vs_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_687_; 
v_ks_668_ = lean_ctor_get(v_x_617_, 0);
v_vs_669_ = lean_ctor_get(v_x_617_, 1);
v_isSharedCheck_687_ = !lean_is_exclusive(v_x_617_);
if (v_isSharedCheck_687_ == 0)
{
v___x_671_ = v_x_617_;
v_isShared_672_ = v_isSharedCheck_687_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_vs_669_);
lean_inc(v_ks_668_);
lean_dec(v_x_617_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_687_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_ks_668_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_vs_669_);
v___x_674_ = v_reuseFailAlloc_686_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v_newNode_675_; size_t v___x_676_; uint8_t v___x_677_; 
v_newNode_675_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7___redArg(v___x_674_, v_x_620_, v_x_621_);
v___x_676_ = ((size_t)7ULL);
v___x_677_ = lean_usize_dec_le(v___x_676_, v_x_619_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_678_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_675_);
v___x_679_ = lean_unsigned_to_nat(4u);
v___x_680_ = lean_nat_dec_lt(v___x_678_, v___x_679_);
lean_dec(v___x_678_);
if (v___x_680_ == 0)
{
lean_object* v_ks_681_; lean_object* v_vs_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_ks_681_ = lean_ctor_get(v_newNode_675_, 0);
lean_inc_ref(v_ks_681_);
v_vs_682_ = lean_ctor_get(v_newNode_675_, 1);
lean_inc_ref(v_vs_682_);
lean_dec_ref(v_newNode_675_);
v___x_683_ = lean_unsigned_to_nat(0u);
v___x_684_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
v___x_685_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_x_619_, v_ks_681_, v_vs_682_, v___x_683_, v___x_684_);
lean_dec_ref(v_vs_682_);
lean_dec_ref(v_ks_681_);
return v___x_685_;
}
else
{
return v_newNode_675_;
}
}
else
{
return v_newNode_675_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_617_ = stack[0].m_obj;
size_t v_x_618_ = stack[1].m_num;
size_t v_x_619_ = stack[2].m_num;
lean_object* v_x_620_ = stack[3].m_obj;
lean_object* v_x_621_ = stack[4].m_obj;
lean_object* v_res_688_;
v_res_688_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_617_, v_x_618_, v_x_619_, v_x_620_, v_x_621_);
stack->m_obj
 = v_res_688_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(size_t v_depth_689_, lean_object* v_keys_690_, lean_object* v_vals_691_, lean_object* v_i_692_, lean_object* v_entries_693_){
_start:
{
lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_694_ = lean_array_get_size(v_keys_690_);
v___x_695_ = lean_nat_dec_lt(v_i_692_, v___x_694_);
if (v___x_695_ == 0)
{
lean_dec(v_i_692_);
return v_entries_693_;
}
else
{
lean_object* v_k_696_; lean_object* v_v_697_; uint64_t v___x_698_; size_t v_h_699_; size_t v___x_700_; lean_object* v___x_701_; size_t v___x_702_; size_t v___x_703_; size_t v___x_704_; size_t v_h_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_k_696_ = lean_array_fget_borrowed(v_keys_690_, v_i_692_);
v_v_697_ = lean_array_fget_borrowed(v_vals_691_, v_i_692_);
v___x_698_ = lean_string_hash(v_k_696_);
v_h_699_ = lean_uint64_to_usize(v___x_698_);
v___x_700_ = ((size_t)5ULL);
v___x_701_ = lean_unsigned_to_nat(1u);
v___x_702_ = ((size_t)1ULL);
v___x_703_ = lean_usize_sub(v_depth_689_, v___x_702_);
v___x_704_ = lean_usize_mul(v___x_700_, v___x_703_);
v_h_705_ = lean_usize_shift_right(v_h_699_, v___x_704_);
v___x_706_ = lean_nat_add(v_i_692_, v___x_701_);
lean_dec(v_i_692_);
lean_inc(v_v_697_);
lean_inc(v_k_696_);
v___x_707_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_entries_693_, v_h_705_, v_depth_689_, v_k_696_, v_v_697_);
v_i_692_ = v___x_706_;
v_entries_693_ = v___x_707_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_689_ = stack[0].m_num;
lean_object* v_keys_690_ = stack[1].m_obj;
lean_object* v_vals_691_ = stack[2].m_obj;
lean_object* v_i_692_ = stack[3].m_obj;
lean_object* v_entries_693_ = stack[4].m_obj;
lean_object* v_res_709_;
v_res_709_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_depth_689_, v_keys_690_, v_vals_691_, v_i_692_, v_entries_693_);
stack->m_obj
 = v_res_709_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_depth_710_, lean_object* v_keys_711_, lean_object* v_vals_712_, lean_object* v_i_713_, lean_object* v_entries_714_){
_start:
{
size_t v_depth_boxed_715_; lean_object* v_res_716_; 
v_depth_boxed_715_ = lean_unbox_usize(v_depth_710_);
lean_dec(v_depth_710_);
v_res_716_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_depth_boxed_715_, v_keys_711_, v_vals_712_, v_i_713_, v_entries_714_);
lean_dec_ref(v_vals_712_);
lean_dec_ref(v_keys_711_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_x_717_, lean_object* v_x_718_, lean_object* v_x_719_, lean_object* v_x_720_, lean_object* v_x_721_){
_start:
{
size_t v_x_897__boxed_722_; size_t v_x_898__boxed_723_; lean_object* v_res_724_; 
v_x_897__boxed_722_ = lean_unbox_usize(v_x_718_);
lean_dec(v_x_718_);
v_x_898__boxed_723_ = lean_unbox_usize(v_x_719_);
lean_dec(v_x_719_);
v_res_724_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_717_, v_x_897__boxed_722_, v_x_898__boxed_723_, v_x_720_, v_x_721_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* v_x_725_, lean_object* v_x_726_, lean_object* v_x_727_){
_start:
{
uint64_t v___x_728_; size_t v___x_729_; size_t v___x_730_; lean_object* v___x_731_; 
v___x_728_ = lean_string_hash(v_x_726_);
v___x_729_ = lean_uint64_to_usize(v___x_728_);
v___x_730_ = ((size_t)1ULL);
v___x_731_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_725_, v___x_729_, v___x_730_, v_x_726_, v_x_727_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_734_){
_start:
{
lean_object* v___x_735_; 
lean_inc(v_params_734_);
v___x_735_ = l_Lean_Lsp_instFromJsonRpcCallParams_fromJson(v_params_734_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_751_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_751_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_751_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_751_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
uint8_t v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_740_ = 3;
v___x_741_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_742_ = l_Lean_Json_compress(v_params_734_);
v___x_743_ = lean_string_append(v___x_741_, v___x_742_);
lean_dec_ref(v___x_742_);
v___x_744_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__1));
v___x_745_ = lean_string_append(v___x_743_, v___x_744_);
v___x_746_ = lean_string_append(v___x_745_, v_a_736_);
lean_dec(v_a_736_);
v___x_747_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set_uint8(v___x_747_, sizeof(void*)*1, v___x_740_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_747_);
v___x_749_ = v___x_738_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec(v_params_734_);
v_a_752_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_735_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_735_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_760_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0(v_params_760_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
lean_ctor_set_tag(v___x_765_, 1);
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
v_a_771_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_762_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_762_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set_tag(v___x_773_, 0);
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_760_ = stack[0].m_obj;
lean_object* v_res_779_;
v_res_779_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_760_);
stack->m_obj
 = v_res_779_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_780_);
return v_res_782_;
}
}
lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_783_, lean_object* v___f_784_, lean_object* v_j_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_785_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_790_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
lean_inc_ref(v___y_786_);
v___x_790_ = lean_apply_3(v_handler_783_, v_a_789_, v___y_786_, lean_box(0));
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_799_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_799_ == 0)
{
v___x_793_ = v___x_790_;
v_isShared_794_ = v_isSharedCheck_799_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_799_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_795_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_784_, v_a_791_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_795_);
v___x_797_ = v___x_793_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec_ref(v___f_784_);
v_a_800_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_790_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_790_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
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
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref(v___f_784_);
lean_dec_ref(v_handler_783_);
v_a_808_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_788_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_788_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_handler_783_ = stack[0].m_obj;
lean_object* v___f_784_ = stack[1].m_obj;
lean_object* v_j_785_ = stack[2].m_obj;
lean_object* v___y_786_ = stack[3].m_obj;
lean_object* v_res_816_;
v_res_816_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2(v_handler_783_, v___f_784_, v_j_785_, v___y_786_);
stack->m_obj
 = v_res_816_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_817_, lean_object* v___f_818_, lean_object* v_j_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2(v_handler_817_, v___f_818_, v_j_819_, v___y_820_);
lean_dec_ref(v___y_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0(v_j_823_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_824_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_824_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_842_; 
v_a_833_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_842_ == 0)
{
v___x_835_ = v___x_824_;
v_isShared_836_ = v_isSharedCheck_842_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_824_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_842_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v_toTextDocumentPositionParams_837_; lean_object* v_textDocument_838_; lean_object* v___x_840_; 
v_toTextDocumentPositionParams_837_ = lean_ctor_get(v_a_833_, 0);
lean_inc_ref(v_toTextDocumentPositionParams_837_);
lean_dec(v_a_833_);
v_textDocument_838_ = lean_ctor_get(v_toTextDocumentPositionParams_837_, 0);
lean_inc_ref(v_textDocument_838_);
lean_dec_ref(v_toTextDocumentPositionParams_837_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v_textDocument_838_);
v___x_840_ = v___x_835_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_textDocument_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_keys_843_, lean_object* v_i_844_, lean_object* v_k_845_){
_start:
{
lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_846_ = lean_array_get_size(v_keys_843_);
v___x_847_ = lean_nat_dec_lt(v_i_844_, v___x_846_);
if (v___x_847_ == 0)
{
lean_dec(v_i_844_);
return v___x_847_;
}
else
{
lean_object* v_k_x27_848_; uint8_t v___x_849_; 
v_k_x27_848_ = lean_array_fget_borrowed(v_keys_843_, v_i_844_);
v___x_849_ = lean_string_dec_eq(v_k_845_, v_k_x27_848_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_unsigned_to_nat(1u);
v___x_851_ = lean_nat_add(v_i_844_, v___x_850_);
lean_dec(v_i_844_);
v_i_844_ = v___x_851_;
goto _start;
}
else
{
lean_dec(v_i_844_);
return v___x_847_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_843_ = stack[0].m_obj;
lean_object* v_i_844_ = stack[1].m_obj;
lean_object* v_k_845_ = stack[2].m_obj;
uint8_t v_res_853_;
v_res_853_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(v_keys_843_, v_i_844_, v_k_845_);
stack->m_num = v_res_853_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_keys_854_, lean_object* v_i_855_, lean_object* v_k_856_){
_start:
{
uint8_t v_res_857_; lean_object* v_r_858_; 
v_res_857_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(v_keys_854_, v_i_855_, v_k_856_);
lean_dec_ref(v_k_856_);
lean_dec_ref(v_keys_854_);
v_r_858_ = lean_box(v_res_857_);
return v_r_858_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object* v_x_859_, size_t v_x_860_, lean_object* v_x_861_){
_start:
{
if (lean_obj_tag(v_x_859_) == 0)
{
lean_object* v_es_862_; lean_object* v___x_863_; size_t v___x_864_; size_t v___x_865_; lean_object* v_j_866_; lean_object* v___x_867_; 
v_es_862_ = lean_ctor_get(v_x_859_, 0);
v___x_863_ = lean_box(2);
v___x_864_ = ((size_t)31ULL);
v___x_865_ = lean_usize_land(v_x_860_, v___x_864_);
v_j_866_ = lean_usize_to_nat(v___x_865_);
v___x_867_ = lean_array_get_borrowed(v___x_863_, v_es_862_, v_j_866_);
lean_dec(v_j_866_);
switch(lean_obj_tag(v___x_867_))
{
case 0:
{
lean_object* v_key_868_; uint8_t v___x_869_; 
v_key_868_ = lean_ctor_get(v___x_867_, 0);
v___x_869_ = lean_string_dec_eq(v_x_861_, v_key_868_);
return v___x_869_;
}
case 1:
{
lean_object* v_node_870_; size_t v___x_871_; size_t v___x_872_; 
v_node_870_ = lean_ctor_get(v___x_867_, 0);
v___x_871_ = ((size_t)5ULL);
v___x_872_ = lean_usize_shift_right(v_x_860_, v___x_871_);
v_x_859_ = v_node_870_;
v_x_860_ = v___x_872_;
goto _start;
}
default: 
{
uint8_t v___x_874_; 
v___x_874_ = 0;
return v___x_874_;
}
}
}
else
{
lean_object* v_ks_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v_ks_875_ = lean_ctor_get(v_x_859_, 0);
v___x_876_ = lean_unsigned_to_nat(0u);
v___x_877_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(v_ks_875_, v___x_876_, v_x_861_);
return v___x_877_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_859_ = stack[0].m_obj;
size_t v_x_860_ = stack[1].m_num;
lean_object* v_x_861_ = stack[2].m_obj;
uint8_t v_res_878_;
v_res_878_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_859_, v_x_860_, v_x_861_);
stack->m_num = v_res_878_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_x_879_, lean_object* v_x_880_, lean_object* v_x_881_){
_start:
{
size_t v_x_1461__boxed_882_; uint8_t v_res_883_; lean_object* v_r_884_; 
v_x_1461__boxed_882_ = lean_unbox_usize(v_x_880_);
lean_dec(v_x_880_);
v_res_883_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_879_, v_x_1461__boxed_882_, v_x_881_);
lean_dec_ref(v_x_881_);
lean_dec_ref(v_x_879_);
v_r_884_ = lean_box(v_res_883_);
return v_r_884_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_885_, lean_object* v_x_886_){
_start:
{
uint64_t v___x_887_; size_t v___x_888_; uint8_t v___x_889_; 
v___x_887_ = lean_string_hash(v_x_886_);
v___x_888_ = lean_uint64_to_usize(v___x_887_);
v___x_889_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_885_, v___x_888_, v_x_886_);
return v___x_889_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_885_ = stack[0].m_obj;
lean_object* v_x_886_ = stack[1].m_obj;
uint8_t v_res_890_;
v_res_890_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_885_, v_x_886_);
stack->m_num = v_res_890_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_x_891_, lean_object* v_x_892_){
_start:
{
uint8_t v_res_893_; lean_object* v_r_894_; 
v_res_893_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_891_, v_x_892_);
lean_dec_ref(v_x_892_);
lean_dec_ref(v_x_891_);
v_r_894_ = lean_box(v_res_893_);
return v_r_894_;
}
}
lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0(lean_object* v_method_899_, lean_object* v_handler_900_, lean_object* v_serialize_x3f_901_){
_start:
{
lean_object* v___f_903_; uint8_t v___x_904_; 
v___f_903_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__0));
v___x_904_ = l_Lean_initializing();
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
lean_dec(v_serialize_x3f_901_);
lean_dec_ref(v_handler_900_);
v___x_905_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__1));
v___x_906_ = lean_string_append(v___x_905_, v_method_899_);
lean_dec_ref(v_method_899_);
v___x_907_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__2));
v___x_908_ = lean_string_append(v___x_906_, v___x_907_);
v___x_909_ = lean_mk_io_user_error(v___x_908_);
v___x_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
return v___x_910_;
}
else
{
lean_object* v___x_911_; lean_object* v___f_912_; lean_object* v___f_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_911_ = lean_box(v___x_904_);
v___f_912_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_912_, 0, v_serialize_x3f_901_);
lean_closure_set(v___f_912_, 1, v___x_911_);
v___f_913_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_913_, 0, v_handler_900_);
lean_closure_set(v___f_913_, 1, v___f_912_);
v___x_914_ = l_Lean_Server_requestHandlers;
v___x_915_ = lean_st_ref_get(v___x_914_);
v___x_916_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_915_, v_method_899_);
lean_dec(v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_917_ = lean_st_ref_take(v___x_914_);
v___x_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_918_, 0, v___f_903_);
lean_ctor_set(v___x_918_, 1, v___f_913_);
v___x_919_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_917_, v_method_899_, v___x_918_);
v___x_920_ = lean_st_ref_put(v___x_914_, v___x_919_);
v___x_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
return v___x_921_;
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec_ref(v___f_913_);
v___x_922_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__1));
v___x_923_ = lean_string_append(v___x_922_, v_method_899_);
lean_dec_ref(v_method_899_);
v___x_924_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__3));
v___x_925_ = lean_string_append(v___x_923_, v___x_924_);
v___x_926_ = lean_mk_io_user_error(v___x_925_);
v___x_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
return v___x_927_;
}
}
}
}
LEAN_EXPORT void l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_899_ = stack[0].m_obj;
lean_object* v_handler_900_ = stack[1].m_obj;
lean_object* v_serialize_x3f_901_ = stack[2].m_obj;
lean_object* v_res_928_;
v_res_928_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0(v_method_899_, v_handler_900_, v_serialize_x3f_901_);
stack->m_obj
 = v_res_928_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_929_, lean_object* v_handler_930_, lean_object* v_serialize_x3f_931_, lean_object* v_a_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0(v_method_929_, v_handler_930_, v_serialize_x3f_931_);
return v_res_933_;
}
}
lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_937_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_));
v___x_938_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_));
v___x_939_ = lean_box(0);
v___x_940_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0(v___x_937_, v___x_938_, v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_941_;
v_res_941_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_();
stack->m_obj
 = v_res_941_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2____boxed(lean_object* v_a_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_();
return v_res_943_;
}
}
lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_944_, lean_object* v_a_945_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_944_);
return v___x_947_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_944_ = stack[0].m_obj;
lean_object* v_a_945_ = stack[1].m_obj;
lean_object* v_res_948_;
v_res_948_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1(v_params_944_, v_a_945_);
stack->m_obj
 = v_res_948_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1(v_params_949_, v_a_950_);
lean_dec_ref(v_a_950_);
return v_res_952_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_953_, lean_object* v_x_954_, lean_object* v_x_955_){
_start:
{
uint8_t v___x_956_; 
v___x_956_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_954_, v_x_955_);
return v___x_956_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_954_ = stack[1].m_obj;
lean_object* v_x_955_ = stack[2].m_obj;
uint8_t v_res_957_;
v_res_957_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2(lean_box(0), v_x_954_, v_x_955_);
stack->m_num = v_res_957_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_958_, lean_object* v_x_959_, lean_object* v_x_960_){
_start:
{
uint8_t v_res_961_; lean_object* v_r_962_; 
v_res_961_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_958_, v_x_959_, v_x_960_);
lean_dec_ref(v_x_960_);
lean_dec_ref(v_x_959_);
v_r_962_ = lean_box(v_res_961_);
return v_r_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_00_u03b2_963_, lean_object* v_x_964_, lean_object* v_x_965_, lean_object* v_x_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_964_, v_x_965_, v_x_966_);
return v___x_967_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object* v_00_u03b2_968_, lean_object* v_x_969_, size_t v_x_970_, lean_object* v_x_971_){
_start:
{
uint8_t v___x_972_; 
v___x_972_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_969_, v_x_970_, v_x_971_);
return v___x_972_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_969_ = stack[1].m_obj;
size_t v_x_970_ = stack[2].m_num;
lean_object* v_x_971_ = stack[3].m_obj;
uint8_t v_res_973_;
v_res_973_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_box(0), v_x_969_, v_x_970_, v_x_971_);
stack->m_num = v_res_973_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_974_, lean_object* v_x_975_, lean_object* v_x_976_, lean_object* v_x_977_){
_start:
{
size_t v_x_1697__boxed_978_; uint8_t v_res_979_; lean_object* v_r_980_; 
v_x_1697__boxed_978_ = lean_unbox_usize(v_x_976_);
lean_dec(v_x_976_);
v_res_979_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_00_u03b2_974_, v_x_975_, v_x_1697__boxed_978_, v_x_977_);
lean_dec_ref(v_x_977_);
lean_dec_ref(v_x_975_);
v_r_980_ = lean_box(v_res_979_);
return v_r_980_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* v_00_u03b2_981_, lean_object* v_x_982_, size_t v_x_983_, size_t v_x_984_, lean_object* v_x_985_, lean_object* v_x_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_982_, v_x_983_, v_x_984_, v_x_985_, v_x_986_);
return v___x_987_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_982_ = stack[1].m_obj;
size_t v_x_983_ = stack[2].m_num;
size_t v_x_984_ = stack[3].m_num;
lean_object* v_x_985_ = stack[4].m_obj;
lean_object* v_x_986_ = stack[5].m_obj;
lean_object* v_res_988_;
v_res_988_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_box(0), v_x_982_, v_x_983_, v_x_984_, v_x_985_, v_x_986_);
stack->m_obj
 = v_res_988_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_989_, lean_object* v_x_990_, lean_object* v_x_991_, lean_object* v_x_992_, lean_object* v_x_993_, lean_object* v_x_994_){
_start:
{
size_t v_x_1715__boxed_995_; size_t v_x_1716__boxed_996_; lean_object* v_res_997_; 
v_x_1715__boxed_995_ = lean_unbox_usize(v_x_991_);
lean_dec(v_x_991_);
v_x_1716__boxed_996_ = lean_unbox_usize(v_x_992_);
lean_dec(v_x_992_);
v_res_997_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_989_, v_x_990_, v_x_1715__boxed_995_, v_x_1716__boxed_996_, v_x_993_, v_x_994_);
return v_res_997_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_998_, lean_object* v_keys_999_, lean_object* v_vals_1000_, lean_object* v_heq_1001_, lean_object* v_i_1002_, lean_object* v_k_1003_){
_start:
{
uint8_t v___x_1004_; 
v___x_1004_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(v_keys_999_, v_i_1002_, v_k_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_999_ = stack[1].m_obj;
lean_object* v_vals_1000_ = stack[2].m_obj;
lean_object* v_i_1002_ = stack[4].m_obj;
lean_object* v_k_1003_ = stack[5].m_obj;
uint8_t v_res_1005_;
v_res_1005_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4(lean_box(0), v_keys_999_, v_vals_1000_, lean_box(0), v_i_1002_, v_k_1003_);
stack->m_num = v_res_1005_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1006_, lean_object* v_keys_1007_, lean_object* v_vals_1008_, lean_object* v_heq_1009_, lean_object* v_i_1010_, lean_object* v_k_1011_){
_start:
{
uint8_t v_res_1012_; lean_object* v_r_1013_; 
v_res_1012_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4(v_00_u03b2_1006_, v_keys_1007_, v_vals_1008_, v_heq_1009_, v_i_1010_, v_k_1011_);
lean_dec_ref(v_k_1011_);
lean_dec_ref(v_vals_1008_);
lean_dec_ref(v_keys_1007_);
v_r_1013_ = lean_box(v_res_1012_);
return v_r_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_1014_, lean_object* v_n_1015_, lean_object* v_k_1016_, lean_object* v_v_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7___redArg(v_n_1015_, v_k_1016_, v_v_1017_);
return v___x_1018_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_1019_, size_t v_depth_1020_, lean_object* v_keys_1021_, lean_object* v_vals_1022_, lean_object* v_heq_1023_, lean_object* v_i_1024_, lean_object* v_entries_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_depth_1020_, v_keys_1021_, v_vals_1022_, v_i_1024_, v_entries_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1020_ = stack[1].m_num;
lean_object* v_keys_1021_ = stack[2].m_obj;
lean_object* v_vals_1022_ = stack[3].m_obj;
lean_object* v_i_1024_ = stack[5].m_obj;
lean_object* v_entries_1025_ = stack[6].m_obj;
lean_object* v_res_1027_;
v_res_1027_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_box(0), v_depth_1020_, v_keys_1021_, v_vals_1022_, lean_box(0), v_i_1024_, v_entries_1025_);
stack->m_obj
 = v_res_1027_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1028_, lean_object* v_depth_1029_, lean_object* v_keys_1030_, lean_object* v_vals_1031_, lean_object* v_heq_1032_, lean_object* v_i_1033_, lean_object* v_entries_1034_){
_start:
{
size_t v_depth_boxed_1035_; lean_object* v_res_1036_; 
v_depth_boxed_1035_ = lean_unbox_usize(v_depth_1029_);
lean_dec(v_depth_1029_);
v_res_1036_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(v_00_u03b2_1028_, v_depth_boxed_1035_, v_keys_1030_, v_vals_1031_, v_heq_1032_, v_i_1033_, v_entries_1034_);
lean_dec_ref(v_vals_1031_);
lean_dec_ref(v_keys_1030_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8(lean_object* v_00_u03b2_1037_, lean_object* v_x_1038_, lean_object* v_x_1039_, lean_object* v_x_1040_, lean_object* v_x_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8___redArg(v_x_1038_, v_x_1039_, v_x_1040_, v_x_1041_);
return v___x_1042_;
}
}
uint8_t l_Lean_Server_wrapRpcProcedure___redArg___lam__0(uint64_t v_x_1043_, uint64_t v_y_1044_){
_start:
{
uint8_t v___x_1045_; 
v___x_1045_ = lean_uint64_dec_lt(v_x_1043_, v_y_1044_);
if (v___x_1045_ == 0)
{
uint8_t v___x_1046_; 
v___x_1046_ = lean_uint64_dec_eq(v_x_1043_, v_y_1044_);
if (v___x_1046_ == 0)
{
uint8_t v___x_1047_; 
v___x_1047_ = 2;
return v___x_1047_;
}
else
{
uint8_t v___x_1048_; 
v___x_1048_ = 1;
return v___x_1048_;
}
}
else
{
uint8_t v___x_1049_; 
v___x_1049_ = 0;
return v___x_1049_;
}
}
}
LEAN_EXPORT void l_Lean_Server_wrapRpcProcedure___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_1043_ = stack[0].m_num;
uint64_t v_y_1044_ = stack[1].m_num;
uint8_t v_res_1050_;
v_res_1050_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__0(v_x_1043_, v_y_1044_);
stack->m_num = v_res_1050_;
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__0___boxed(lean_object* v_x_1051_, lean_object* v_y_1052_){
_start:
{
uint64_t v_x_boxed_1053_; uint64_t v_y_boxed_1054_; uint8_t v_res_1055_; lean_object* v_r_1056_; 
v_x_boxed_1053_ = lean_unbox_uint64(v_x_1051_);
lean_dec_ref(v_x_1051_);
v_y_boxed_1054_ = lean_unbox_uint64(v_y_1052_);
lean_dec_ref(v_y_1052_);
v_res_1055_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__0(v_x_boxed_1053_, v_y_boxed_1054_);
v_r_1056_ = lean_box(v_res_1055_);
return v_r_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__1(lean_object* v_expireTime_1057_, lean_object* v_x_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v_x_1058_);
lean_ctor_set(v___x_1059_, 1, v_expireTime_1057_);
return v___x_1059_;
}
}
lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__2(lean_object* v_val_1061_, lean_object* v_inst_1062_, lean_object* v_x_1063_, lean_object* v___y_1064_){
_start:
{
if (lean_obj_tag(v_x_1063_) == 0)
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec_ref(v_inst_1062_);
v_a_1066_ = lean_ctor_get(v_x_1063_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_x_1063_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v_x_1063_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v_x_1063_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
lean_ctor_set_tag(v___x_1068_, 1);
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1092_; 
v_a_1074_ = lean_ctor_get(v_x_1063_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_x_1063_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1076_ = v_x_1063_;
v_isShared_1077_ = v_isSharedCheck_1092_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v_x_1063_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1092_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v_rpcEncode_1079_; lean_object* v_objects_1080_; lean_object* v_expireTime_1081_; lean_object* v___f_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v_fst_1086_; lean_object* v_snd_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1078_ = lean_st_ref_take(v_val_1061_);
v_rpcEncode_1079_ = lean_ctor_get(v_inst_1062_, 0);
lean_inc_ref(v_rpcEncode_1079_);
lean_dec_ref(v_inst_1062_);
v_objects_1080_ = lean_ctor_get(v___x_1078_, 0);
lean_inc_ref(v_objects_1080_);
v_expireTime_1081_ = lean_ctor_get(v___x_1078_, 1);
lean_inc(v_expireTime_1081_);
lean_dec(v___x_1078_);
v___f_1082_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1082_, 0, v_expireTime_1081_);
v___x_1083_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__2___closed__0));
v___x_1084_ = lean_apply_2(v_rpcEncode_1079_, v_a_1074_, v_objects_1080_);
v___x_1085_ = l_Prod_map___redArg(v___x_1083_, v___f_1082_, v___x_1084_);
v_fst_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_fst_1086_);
v_snd_1087_ = lean_ctor_get(v___x_1085_, 1);
lean_inc(v_snd_1087_);
lean_dec_ref(v___x_1085_);
v___x_1088_ = lean_st_ref_put(v_val_1061_, v_snd_1087_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set_tag(v___x_1076_, 0);
lean_ctor_set(v___x_1076_, 0, v_fst_1086_);
v___x_1090_ = v___x_1076_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_fst_1086_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_wrapRpcProcedure___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1061_ = stack[0].m_obj;
lean_object* v_inst_1062_ = stack[1].m_obj;
lean_object* v_x_1063_ = stack[2].m_obj;
lean_object* v___y_1064_ = stack[3].m_obj;
lean_object* v_res_1093_;
v_res_1093_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__2(v_val_1061_, v_inst_1062_, v_x_1063_, v___y_1064_);
stack->m_obj
 = v_res_1093_;
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__2___boxed(lean_object* v_val_1094_, lean_object* v_inst_1095_, lean_object* v_x_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__2(v_val_1094_, v_inst_1095_, v_x_1096_, v___y_1097_);
lean_dec_ref(v___y_1097_);
lean_dec(v_val_1094_);
return v_res_1099_;
}
}
lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__3(lean_object* v___f_1107_, lean_object* v_inst_1108_, lean_object* v_inst_1109_, lean_object* v_method_1110_, lean_object* v_handler_1111_, uint64_t v_seshId_1112_, lean_object* v_j_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_rpcSessions_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v_rpcSessions_1116_ = lean_ctor_get(v___y_1114_, 0);
v___x_1117_ = lean_box_uint64(v_seshId_1112_);
lean_inc(v_rpcSessions_1116_);
v___x_1118_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_1107_, v_rpcSessions_1116_, v___x_1117_);
if (lean_obj_tag(v___x_1118_) == 1)
{
lean_object* v_val_1119_; lean_object* v___f_1120_; lean_object* v___x_1121_; lean_object* v_rpcDecode_1122_; lean_object* v_objects_1123_; lean_object* v___x_1124_; 
v_val_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc_n(v_val_1119_, 2);
lean_dec_ref_known(v___x_1118_, 1);
v___f_1120_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_1120_, 0, v_val_1119_);
lean_closure_set(v___f_1120_, 1, v_inst_1108_);
v___x_1121_ = lean_st_ref_get(v_val_1119_);
lean_dec(v_val_1119_);
v_rpcDecode_1122_ = lean_ctor_get(v_inst_1109_, 1);
lean_inc_ref(v_rpcDecode_1122_);
lean_dec_ref(v_inst_1109_);
v_objects_1123_ = lean_ctor_get(v___x_1121_, 0);
lean_inc_ref(v_objects_1123_);
lean_dec(v___x_1121_);
lean_inc(v_j_1113_);
v___x_1124_ = lean_apply_2(v_rpcDecode_1122_, v_j_1113_, v_objects_1123_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1145_; 
lean_dec_ref(v___f_1120_);
lean_dec_ref(v_handler_1111_);
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1145_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1145_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
uint8_t v___x_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1129_ = 3;
v___x_1130_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__0));
v___x_1131_ = 1;
v___x_1132_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_1110_, v___x_1131_);
v___x_1133_ = lean_string_append(v___x_1130_, v___x_1132_);
lean_dec_ref(v___x_1132_);
v___x_1134_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__1));
v___x_1135_ = lean_string_append(v___x_1133_, v___x_1134_);
v___x_1136_ = l_Lean_Json_compress(v_j_1113_);
v___x_1137_ = lean_string_append(v___x_1135_, v___x_1136_);
lean_dec_ref(v___x_1136_);
v___x_1138_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__2));
v___x_1139_ = lean_string_append(v___x_1137_, v___x_1138_);
v___x_1140_ = lean_string_append(v___x_1139_, v_a_1125_);
lean_dec(v_a_1125_);
v___x_1141_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*1, v___x_1129_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set_tag(v___x_1127_, 1);
lean_ctor_set(v___x_1127_, 0, v___x_1141_);
v___x_1143_ = v___x_1127_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1147_; 
lean_dec(v_j_1113_);
lean_dec(v_method_1110_);
v_a_1146_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1124_, 1);
lean_inc_ref(v___y_1114_);
v___x_1147_ = lean_apply_3(v_handler_1111_, v_a_1146_, v___y_1114_, lean_box(0));
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1149_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref_known(v___x_1147_, 1);
v___x_1149_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_a_1148_, v___f_1120_, v___y_1114_);
return v___x_1149_;
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec_ref(v___f_1120_);
v_a_1150_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1147_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1147_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
else
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
lean_dec(v___x_1118_);
lean_dec(v_j_1113_);
lean_dec_ref(v_handler_1111_);
lean_dec(v_method_1110_);
lean_dec_ref(v_inst_1109_);
lean_dec_ref(v_inst_1108_);
v___x_1158_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__4));
v___x_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
return v___x_1159_;
}
}
}
LEAN_EXPORT void l_Lean_Server_wrapRpcProcedure___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1107_ = stack[0].m_obj;
lean_object* v_inst_1108_ = stack[1].m_obj;
lean_object* v_inst_1109_ = stack[2].m_obj;
lean_object* v_method_1110_ = stack[3].m_obj;
lean_object* v_handler_1111_ = stack[4].m_obj;
uint64_t v_seshId_1112_ = stack[5].m_num;
lean_object* v_j_1113_ = stack[6].m_obj;
lean_object* v___y_1114_ = stack[7].m_obj;
lean_object* v_res_1160_;
v_res_1160_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__3(v___f_1107_, v_inst_1108_, v_inst_1109_, v_method_1110_, v_handler_1111_, v_seshId_1112_, v_j_1113_, v___y_1114_);
stack->m_obj
 = v_res_1160_;
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__3___boxed(lean_object* v___f_1161_, lean_object* v_inst_1162_, lean_object* v_inst_1163_, lean_object* v_method_1164_, lean_object* v_handler_1165_, lean_object* v_seshId_1166_, lean_object* v_j_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
uint64_t v_seshId_boxed_1170_; lean_object* v_res_1171_; 
v_seshId_boxed_1170_ = lean_unbox_uint64(v_seshId_1166_);
lean_dec_ref(v_seshId_1166_);
v_res_1171_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__3(v___f_1161_, v_inst_1162_, v_inst_1163_, v_method_1164_, v_handler_1165_, v_seshId_boxed_1170_, v_j_1167_, v___y_1168_);
lean_dec_ref(v___y_1168_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg(lean_object* v_method_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_, lean_object* v_handler_1176_){
_start:
{
lean_object* v___f_1177_; lean_object* v___f_1178_; 
v___f_1177_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___redArg___closed__0));
v___f_1178_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___boxed), 9, 5);
lean_closure_set(v___f_1178_, 0, v___f_1177_);
lean_closure_set(v___f_1178_, 1, v_inst_1175_);
lean_closure_set(v___f_1178_, 2, v_inst_1174_);
lean_closure_set(v___f_1178_, 3, v_method_1173_);
lean_closure_set(v___f_1178_, 4, v_handler_1176_);
return v___f_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure(lean_object* v_method_1179_, lean_object* v_paramType_1180_, lean_object* v_respType_1181_, lean_object* v_inst_1182_, lean_object* v_inst_1183_, lean_object* v_handler_1184_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_Server_wrapRpcProcedure___redArg(v_method_1179_, v_inst_1182_, v_inst_1183_, v_handler_1184_);
return v___x_1185_;
}
}
lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg(lean_object* v_method_1192_, lean_object* v_inst_1193_, lean_object* v_inst_1194_, lean_object* v_handler_1195_){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v_errMsg_1204_; uint8_t v___x_1205_; 
v___x_1197_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__0));
v___x_1198_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__1));
v___x_1199_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__2));
v___x_1200_ = 1;
lean_inc(v_method_1192_);
v___x_1201_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_1192_, v___x_1200_);
v___x_1202_ = lean_string_append(v___x_1199_, v___x_1201_);
lean_dec_ref(v___x_1201_);
v___x_1203_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__3));
v_errMsg_1204_ = lean_string_append(v___x_1202_, v___x_1203_);
v___x_1205_ = l_Lean_initializing();
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec_ref(v_handler_1195_);
lean_dec_ref(v_inst_1194_);
lean_dec_ref(v_inst_1193_);
lean_dec(v_method_1192_);
v___x_1206_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__4));
v___x_1207_ = lean_string_append(v_errMsg_1204_, v___x_1206_);
v___x_1208_ = lean_mk_io_user_error(v___x_1207_);
v___x_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
else
{
lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1210_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_1211_ = lean_st_ref_get(v___x_1210_);
lean_inc(v_method_1192_);
v___x_1212_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1197_, v___x_1198_, v___x_1211_, v_method_1192_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_dec_ref(v_errMsg_1204_);
lean_inc(v_method_1192_);
v___x_1213_ = l_Lean_Server_wrapRpcProcedure___redArg(v_method_1192_, v_inst_1193_, v_inst_1194_, v_handler_1195_);
v___x_1214_ = lean_st_ref_take(v___x_1210_);
v___x_1215_ = l_Lean_PersistentHashMap_insert___redArg(v___x_1197_, v___x_1198_, v___x_1214_, v_method_1192_, v___x_1213_);
v___x_1216_ = lean_st_ref_put(v___x_1210_, v___x_1215_);
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
return v___x_1217_;
}
else
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_dec_ref(v_handler_1195_);
lean_dec_ref(v_inst_1194_);
lean_dec_ref(v_inst_1193_);
lean_dec(v_method_1192_);
v___x_1218_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__5));
v___x_1219_ = lean_string_append(v_errMsg_1204_, v___x_1218_);
v___x_1220_ = lean_mk_io_user_error(v___x_1219_);
v___x_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
}
}
}
LEAN_EXPORT void l_Lean_Server_registerBuiltinRpcProcedure___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_1192_ = stack[0].m_obj;
lean_object* v_inst_1193_ = stack[1].m_obj;
lean_object* v_inst_1194_ = stack[2].m_obj;
lean_object* v_handler_1195_ = stack[3].m_obj;
lean_object* v_res_1222_;
v_res_1222_ = l_Lean_Server_registerBuiltinRpcProcedure___redArg(v_method_1192_, v_inst_1193_, v_inst_1194_, v_handler_1195_);
stack->m_obj
 = v_res_1222_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg___boxed(lean_object* v_method_1223_, lean_object* v_inst_1224_, lean_object* v_inst_1225_, lean_object* v_handler_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_Server_registerBuiltinRpcProcedure___redArg(v_method_1223_, v_inst_1224_, v_inst_1225_, v_handler_1226_);
return v_res_1228_;
}
}
lean_object* l_Lean_Server_registerBuiltinRpcProcedure(lean_object* v_method_1229_, lean_object* v_paramType_1230_, lean_object* v_respType_1231_, lean_object* v_inst_1232_, lean_object* v_inst_1233_, lean_object* v_handler_1234_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_Server_registerBuiltinRpcProcedure___redArg(v_method_1229_, v_inst_1232_, v_inst_1233_, v_handler_1234_);
return v___x_1236_;
}
}
LEAN_EXPORT void l_Lean_Server_registerBuiltinRpcProcedure_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_1229_ = stack[0].m_obj;
lean_object* v_inst_1232_ = stack[3].m_obj;
lean_object* v_inst_1233_ = stack[4].m_obj;
lean_object* v_handler_1234_ = stack[5].m_obj;
lean_object* v_res_1237_;
v_res_1237_ = l_Lean_Server_registerBuiltinRpcProcedure(v_method_1229_, lean_box(0), lean_box(0), v_inst_1232_, v_inst_1233_, v_handler_1234_);
stack->m_obj
 = v_res_1237_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___boxed(lean_object* v_method_1238_, lean_object* v_paramType_1239_, lean_object* v_respType_1240_, lean_object* v_inst_1241_, lean_object* v_inst_1242_, lean_object* v_handler_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_Server_registerBuiltinRpcProcedure(v_method_1238_, v_paramType_1239_, v_respType_1240_, v_inst_1241_, v_inst_1242_, v_handler_1243_);
return v_res_1245_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(lean_object* v_e_1246_, lean_object* v___y_1247_){
_start:
{
uint8_t v___x_1249_; 
v___x_1249_ = l_Lean_Expr_hasMVar(v_e_1246_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; 
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v_e_1246_);
return v___x_1250_;
}
else
{
lean_object* v___x_1251_; lean_object* v_mctx_1252_; lean_object* v___x_1253_; lean_object* v_fst_1254_; lean_object* v_snd_1255_; lean_object* v___x_1256_; lean_object* v_cache_1257_; lean_object* v_zetaDeltaFVarIds_1258_; lean_object* v_postponed_1259_; lean_object* v_diag_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1269_; 
v___x_1251_ = lean_st_ref_get(v___y_1247_);
v_mctx_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc_ref(v_mctx_1252_);
lean_dec(v___x_1251_);
v___x_1253_ = l_Lean_instantiateMVarsCore(v_mctx_1252_, v_e_1246_);
v_fst_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_fst_1254_);
v_snd_1255_ = lean_ctor_get(v___x_1253_, 1);
lean_inc(v_snd_1255_);
lean_dec_ref(v___x_1253_);
v___x_1256_ = lean_st_ref_take(v___y_1247_);
v_cache_1257_ = lean_ctor_get(v___x_1256_, 1);
v_zetaDeltaFVarIds_1258_ = lean_ctor_get(v___x_1256_, 2);
v_postponed_1259_ = lean_ctor_get(v___x_1256_, 3);
v_diag_1260_ = lean_ctor_get(v___x_1256_, 4);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1269_ == 0)
{
lean_object* v_unused_1270_; 
v_unused_1270_ = lean_ctor_get(v___x_1256_, 0);
lean_dec(v_unused_1270_);
v___x_1262_ = v___x_1256_;
v_isShared_1263_ = v_isSharedCheck_1269_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_diag_1260_);
lean_inc(v_postponed_1259_);
lean_inc(v_zetaDeltaFVarIds_1258_);
lean_inc(v_cache_1257_);
lean_dec(v___x_1256_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1269_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v_snd_1255_);
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_snd_1255_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_cache_1257_);
lean_ctor_set(v_reuseFailAlloc_1268_, 2, v_zetaDeltaFVarIds_1258_);
lean_ctor_set(v_reuseFailAlloc_1268_, 3, v_postponed_1259_);
lean_ctor_set(v_reuseFailAlloc_1268_, 4, v_diag_1260_);
v___x_1265_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = lean_st_ref_put(v___y_1247_, v___x_1265_);
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v_fst_1254_);
return v___x_1267_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1246_ = stack[0].m_obj;
lean_object* v___y_1247_ = stack[1].m_obj;
lean_object* v_res_1271_;
v_res_1271_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(v_e_1246_, v___y_1247_);
stack->m_obj
 = v_res_1271_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg___boxed(lean_object* v_e_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(v_e_1272_, v___y_1273_);
lean_dec(v___y_1273_);
return v_res_1275_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0(lean_object* v_e_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(v_e_1276_, v___y_1280_);
return v___x_1284_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1276_ = stack[0].m_obj;
lean_object* v___y_1277_ = stack[1].m_obj;
lean_object* v___y_1278_ = stack[2].m_obj;
lean_object* v___y_1279_ = stack[3].m_obj;
lean_object* v___y_1280_ = stack[4].m_obj;
lean_object* v___y_1281_ = stack[5].m_obj;
lean_object* v___y_1282_ = stack[6].m_obj;
lean_object* v_res_1285_;
v_res_1285_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0(v_e_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
stack->m_obj
 = v_res_1285_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___boxed(lean_object* v_e_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0(v_e_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
return v_res_1294_;
}
}
lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg(lean_object* v_a_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
return v___x_1303_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1295_ = stack[0].m_obj;
lean_object* v___y_1296_ = stack[1].m_obj;
lean_object* v___y_1297_ = stack[2].m_obj;
lean_object* v___y_1298_ = stack[3].m_obj;
lean_object* v___y_1299_ = stack[4].m_obj;
lean_object* v___y_1300_ = stack[5].m_obj;
lean_object* v___y_1301_ = stack[6].m_obj;
lean_object* v_res_1304_;
v_res_1304_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg(v_a_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
stack->m_obj
 = v_res_1304_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg___boxed(lean_object* v_a_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg(v_a_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
return v_res_1313_;
}
}
lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1(lean_object* v_00_u03b1_1314_, lean_object* v_a_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
return v___x_1323_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1315_ = stack[1].m_obj;
lean_object* v___y_1316_ = stack[2].m_obj;
lean_object* v___y_1317_ = stack[3].m_obj;
lean_object* v___y_1318_ = stack[4].m_obj;
lean_object* v___y_1319_ = stack[5].m_obj;
lean_object* v___y_1320_ = stack[6].m_obj;
lean_object* v___y_1321_ = stack[7].m_obj;
lean_object* v_res_1324_;
v_res_1324_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1(lean_box(0), v_a_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
stack->m_obj
 = v_res_1324_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___boxed(lean_object* v_00_u03b1_1325_, lean_object* v_a_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1(v_00_u03b1_1325_, v_a_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
return v_res_1334_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_);
v___x_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
return v___x_1336_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0);
v___x_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
return v___x_1338_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(lean_object* v_env_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; lean_object* v_nextMacroScope_1343_; lean_object* v_ngen_1344_; lean_object* v_auxDeclNGen_1345_; lean_object* v_traceState_1346_; lean_object* v_recordedDeps_1347_; lean_object* v_messages_1348_; lean_object* v_infoState_1349_; lean_object* v_snapshotTasks_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1361_; 
v___x_1342_ = lean_st_ref_take(v___y_1340_);
v_nextMacroScope_1343_ = lean_ctor_get(v___x_1342_, 1);
v_ngen_1344_ = lean_ctor_get(v___x_1342_, 2);
v_auxDeclNGen_1345_ = lean_ctor_get(v___x_1342_, 3);
v_traceState_1346_ = lean_ctor_get(v___x_1342_, 4);
v_recordedDeps_1347_ = lean_ctor_get(v___x_1342_, 6);
v_messages_1348_ = lean_ctor_get(v___x_1342_, 7);
v_infoState_1349_ = lean_ctor_get(v___x_1342_, 8);
v_snapshotTasks_1350_ = lean_ctor_get(v___x_1342_, 9);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1361_ == 0)
{
lean_object* v_unused_1362_; lean_object* v_unused_1363_; 
v_unused_1362_ = lean_ctor_get(v___x_1342_, 5);
lean_dec(v_unused_1362_);
v_unused_1363_ = lean_ctor_get(v___x_1342_, 0);
lean_dec(v_unused_1363_);
v___x_1352_ = v___x_1342_;
v_isShared_1353_ = v_isSharedCheck_1361_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_snapshotTasks_1350_);
lean_inc(v_infoState_1349_);
lean_inc(v_messages_1348_);
lean_inc(v_recordedDeps_1347_);
lean_inc(v_traceState_1346_);
lean_inc(v_auxDeclNGen_1345_);
lean_inc(v_ngen_1344_);
lean_inc(v_nextMacroScope_1343_);
lean_dec(v___x_1342_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1361_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1354_ = lean_box(0);
v___x_1355_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 5, v___x_1355_);
lean_ctor_set(v___x_1352_, 0, v_env_1339_);
v___x_1357_ = v___x_1352_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_env_1339_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_nextMacroScope_1343_);
lean_ctor_set(v_reuseFailAlloc_1360_, 2, v_ngen_1344_);
lean_ctor_set(v_reuseFailAlloc_1360_, 3, v_auxDeclNGen_1345_);
lean_ctor_set(v_reuseFailAlloc_1360_, 4, v_traceState_1346_);
lean_ctor_set(v_reuseFailAlloc_1360_, 5, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1360_, 6, v_recordedDeps_1347_);
lean_ctor_set(v_reuseFailAlloc_1360_, 7, v_messages_1348_);
lean_ctor_set(v_reuseFailAlloc_1360_, 8, v_infoState_1349_);
lean_ctor_set(v_reuseFailAlloc_1360_, 9, v_snapshotTasks_1350_);
v___x_1357_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = lean_st_ref_put(v___y_1340_, v___x_1357_);
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1354_);
return v___x_1359_;
}
}
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1339_ = stack[0].m_obj;
lean_object* v___y_1340_ = stack[1].m_obj;
lean_object* v_res_1364_;
v_res_1364_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(v_env_1339_, v___y_1340_);
stack->m_obj
 = v_res_1364_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___boxed(lean_object* v_env_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(v_env_1365_, v___y_1366_);
lean_dec(v___y_1366_);
return v_res_1368_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2(lean_object* v_env_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(v_env_1369_, v___y_1371_);
return v___x_1373_;
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1369_ = stack[0].m_obj;
lean_object* v___y_1370_ = stack[1].m_obj;
lean_object* v___y_1371_ = stack[2].m_obj;
lean_object* v_res_1374_;
v_res_1374_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2(v_env_1369_, v___y_1370_, v___y_1371_);
stack->m_obj
 = v_res_1374_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___boxed(lean_object* v_env_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2(v_env_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1379_;
}
}
uint8_t l_Lean_Server_registerRpcProcedure___lam__0(lean_object* v_x_1380_){
_start:
{
uint8_t v___x_1381_; 
v___x_1381_ = 0;
return v___x_1381_;
}
}
LEAN_EXPORT void l_Lean_Server_registerRpcProcedure___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1380_ = stack[0].m_obj;
uint8_t v_res_1382_;
v_res_1382_ = l_Lean_Server_registerRpcProcedure___lam__0(v_x_1380_);
stack->m_num = v_res_1382_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__0___boxed(lean_object* v_x_1383_){
_start:
{
uint8_t v_res_1384_; lean_object* v_r_1385_; 
v_res_1384_ = l_Lean_Server_registerRpcProcedure___lam__0(v_x_1383_);
lean_dec(v_x_1383_);
v_r_1385_ = lean_box(v_res_1384_);
return v_r_1385_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__3));
v___x_1391_ = l_String_toRawSubstring_x27(v___x_1390_);
return v___x_1391_;
}
}
lean_object* l_Lean_Server_registerRpcProcedure___lam__1(lean_object* v___x_1402_, lean_object* v___x_1403_, lean_object* v_method_1404_, lean_object* v___x_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_toCold_1413_; lean_object* v_ref_1414_; lean_object* v_quotContext_1415_; lean_object* v_currMacroScope_1416_; uint8_t v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___y_1436_; lean_object* v___x_1450_; 
v_toCold_1413_ = lean_ctor_get(v___y_1410_, 0);
v_ref_1414_ = lean_ctor_get(v___y_1410_, 2);
v_quotContext_1415_ = lean_ctor_get(v_toCold_1413_, 8);
v_currMacroScope_1416_ = lean_ctor_get(v_toCold_1413_, 9);
v___x_1417_ = 0;
v___x_1418_ = l_Lean_SourceInfo_fromRef(v_ref_1414_, v___x_1417_);
v___x_1419_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__0));
v___x_1420_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__1));
v___x_1421_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__2));
lean_inc_ref_n(v___x_1402_, 2);
v___x_1422_ = l_Lean_Name_mkStr4(v___x_1402_, v___x_1419_, v___x_1420_, v___x_1421_);
v___x_1423_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__3));
v___x_1424_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___lam__1___closed__4, &l_Lean_Server_registerRpcProcedure___lam__1___closed__4_once, _init_l_Lean_Server_registerRpcProcedure___lam__1___closed__4);
v___x_1425_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__5));
lean_inc(v_currMacroScope_1416_);
lean_inc(v_quotContext_1415_);
v___x_1426_ = l_Lean_addMacroScope(v_quotContext_1415_, v___x_1425_, v_currMacroScope_1416_);
v___x_1427_ = l_Lean_Name_mkStr3(v___x_1402_, v___x_1403_, v___x_1423_);
v___x_1428_ = lean_box(0);
lean_inc(v___x_1427_);
v___x_1429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1427_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1427_);
v___x_1431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set(v___x_1431_, 1, v___x_1428_);
v___x_1432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1429_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
lean_inc(v___x_1418_);
v___x_1433_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1418_);
lean_ctor_set(v___x_1433_, 1, v___x_1424_);
lean_ctor_set(v___x_1433_, 2, v___x_1426_);
lean_ctor_set(v___x_1433_, 3, v___x_1432_);
v___x_1434_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__7));
lean_inc(v_method_1404_);
v___x_1450_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_1428_, v_method_1404_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v___x_1451_; 
lean_inc(v_method_1404_);
v___x_1451_ = l_Lean_quoteNameMk(v_method_1404_);
v___y_1436_ = v___x_1451_;
goto v___jp_1435_;
}
else
{
lean_object* v_val_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v_val_1452_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_val_1452_);
lean_dec_ref_known(v___x_1450_, 1);
v___x_1453_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__10));
lean_inc_ref(v___x_1402_);
v___x_1454_ = l_Lean_Name_mkStr4(v___x_1402_, v___x_1419_, v___x_1420_, v___x_1453_);
v___x_1455_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__11));
v___x_1456_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__12));
v___x_1457_ = lean_string_intercalate(v___x_1456_, v_val_1452_);
v___x_1458_ = lean_string_append(v___x_1455_, v___x_1457_);
lean_dec_ref(v___x_1457_);
v___x_1459_ = lean_box(2);
v___x_1460_ = l_Lean_Syntax_mkNameLit(v___x_1458_, v___x_1459_);
v___x_1461_ = lean_unsigned_to_nat(1u);
v___x_1462_ = lean_mk_empty_array_with_capacity(v___x_1461_);
v___x_1463_ = lean_array_push(v___x_1462_, v___x_1460_);
v___x_1464_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1459_);
lean_ctor_set(v___x_1464_, 1, v___x_1454_);
lean_ctor_set(v___x_1464_, 2, v___x_1463_);
v___y_1436_ = v___x_1464_;
goto v___jp_1435_;
}
v___jp_1435_:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; lean_object* v___x_1447_; 
v___x_1437_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__8));
v___x_1438_ = l_Lean_Name_mkStr4(v___x_1402_, v___x_1419_, v___x_1420_, v___x_1437_);
v___x_1439_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___lam__1___closed__9));
lean_inc_n(v___x_1418_, 3);
v___x_1440_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1418_);
lean_ctor_set(v___x_1440_, 1, v___x_1439_);
v___x_1441_ = l_Lean_Syntax_node1(v___x_1418_, v___x_1438_, v___x_1440_);
v___x_1442_ = l_Lean_mkIdent(v_method_1404_);
lean_inc(v___x_1441_);
v___x_1443_ = l_Lean_Syntax_node4(v___x_1418_, v___x_1434_, v___y_1436_, v___x_1441_, v___x_1441_, v___x_1442_);
v___x_1444_ = l_Lean_Syntax_node2(v___x_1418_, v___x_1422_, v___x_1433_, v___x_1443_);
v___x_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1405_);
v___x_1446_ = 1;
v___x_1447_ = l_Lean_Elab_Term_elabTerm(v___x_1444_, v___x_1445_, v___x_1446_, v___x_1446_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec_ref(v___y_1410_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1449_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___x_1447_, 1);
v___x_1449_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(v_a_1448_, v___y_1409_);
return v___x_1449_;
}
else
{
return v___x_1447_;
}
}
}
}
LEAN_EXPORT void l_Lean_Server_registerRpcProcedure___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1402_ = stack[0].m_obj;
lean_object* v___x_1403_ = stack[1].m_obj;
lean_object* v_method_1404_ = stack[2].m_obj;
lean_object* v___x_1405_ = stack[3].m_obj;
lean_object* v___y_1406_ = stack[4].m_obj;
lean_object* v___y_1407_ = stack[5].m_obj;
lean_object* v___y_1408_ = stack[6].m_obj;
lean_object* v___y_1409_ = stack[7].m_obj;
lean_object* v___y_1410_ = stack[8].m_obj;
lean_object* v___y_1411_ = stack[9].m_obj;
lean_object* v_res_1465_;
v_res_1465_ = l_Lean_Server_registerRpcProcedure___lam__1(v___x_1402_, v___x_1403_, v_method_1404_, v___x_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
stack->m_obj
 = v_res_1465_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__1___boxed(lean_object* v___x_1466_, lean_object* v___x_1467_, lean_object* v_method_1468_, lean_object* v___x_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_Server_registerRpcProcedure___lam__1(v___x_1466_, v___x_1467_, v_method_1468_, v___x_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
return v_res_1477_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_);
v___x_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
return v___x_1479_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1480_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1481_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0);
v___x_1482_ = lean_unsigned_to_nat(0u);
v___x_1483_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
lean_ctor_set(v___x_1483_, 2, v___x_1482_);
lean_ctor_set(v___x_1483_, 3, v___x_1482_);
lean_ctor_set(v___x_1483_, 4, v___x_1481_);
lean_ctor_set(v___x_1483_, 5, v___x_1481_);
lean_ctor_set(v___x_1483_, 6, v___x_1481_);
lean_ctor_set(v___x_1483_, 7, v___x_1481_);
lean_ctor_set(v___x_1483_, 8, v___x_1481_);
lean_ctor_set(v___x_1483_, 9, v___x_1481_);
lean_ctor_set(v___x_1483_, 10, v___x_1481_);
lean_ctor_set(v___x_1483_, 11, v___x_1480_);
return v___x_1483_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1484_ = lean_unsigned_to_nat(32u);
v___x_1485_ = lean_mk_empty_array_with_capacity(v___x_1484_);
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
return v___x_1486_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3(void){
_start:
{
size_t v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1487_ = ((size_t)5ULL);
v___x_1488_ = lean_unsigned_to_nat(0u);
v___x_1489_ = lean_unsigned_to_nat(32u);
v___x_1490_ = lean_mk_empty_array_with_capacity(v___x_1489_);
v___x_1491_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2);
v___x_1492_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
lean_ctor_set(v___x_1492_, 1, v___x_1490_);
lean_ctor_set(v___x_1492_, 2, v___x_1488_);
lean_ctor_set(v___x_1492_, 3, v___x_1488_);
lean_ctor_set_usize(v___x_1492_, 4, v___x_1487_);
return v___x_1492_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4(void){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1493_ = lean_box(1);
v___x_1494_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3);
v___x_1495_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0);
v___x_1496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
lean_ctor_set(v___x_1496_, 1, v___x_1494_);
lean_ctor_set(v___x_1496_, 2, v___x_1493_);
return v___x_1496_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3(lean_object* v_msgData_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v___x_1501_; lean_object* v_toCold_1502_; lean_object* v_env_1503_; lean_object* v_options_1504_; uint8_t v___x_1505_; lean_object* v_env_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1501_ = lean_st_ref_get(v___y_1499_);
v_toCold_1502_ = lean_ctor_get(v___y_1498_, 0);
v_env_1503_ = lean_ctor_get(v___x_1501_, 0);
lean_inc_ref(v_env_1503_);
lean_dec(v___x_1501_);
v_options_1504_ = lean_ctor_get(v_toCold_1502_, 2);
v___x_1505_ = 0;
v_env_1506_ = l_Lean_Environment_setRecordingDeps(v_env_1503_, v___x_1505_);
v___x_1507_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1);
v___x_1508_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4);
lean_inc_ref(v_options_1504_);
v___x_1509_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1509_, 0, v_env_1506_);
lean_ctor_set(v___x_1509_, 1, v___x_1507_);
lean_ctor_set(v___x_1509_, 2, v___x_1508_);
lean_ctor_set(v___x_1509_, 3, v_options_1504_);
v___x_1510_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
lean_ctor_set(v___x_1510_, 1, v_msgData_1497_);
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1497_ = stack[0].m_obj;
lean_object* v___y_1498_ = stack[1].m_obj;
lean_object* v___y_1499_ = stack[2].m_obj;
lean_object* v_res_1512_;
v_res_1512_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3(v_msgData_1497_, v___y_1498_, v___y_1499_);
stack->m_obj
 = v_res_1512_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___boxed(lean_object* v_msgData_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3(v_msgData_1513_, v___y_1514_, v___y_1515_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
return v_res_1517_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(lean_object* v_msg_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_ref_1522_; lean_object* v___x_1523_; lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1532_; 
v_ref_1522_ = lean_ctor_get(v___y_1519_, 2);
v___x_1523_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3(v_msg_1518_, v___y_1519_, v___y_1520_);
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1526_ = v___x_1523_;
v_isShared_1527_ = v_isSharedCheck_1532_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1523_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1532_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1528_; lean_object* v___x_1530_; 
lean_inc(v_ref_1522_);
v___x_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1528_, 0, v_ref_1522_);
lean_ctor_set(v___x_1528_, 1, v_a_1524_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set_tag(v___x_1526_, 1);
lean_ctor_set(v___x_1526_, 0, v___x_1528_);
v___x_1530_ = v___x_1526_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1518_ = stack[0].m_obj;
lean_object* v___y_1519_ = stack[1].m_obj;
lean_object* v___y_1520_ = stack[2].m_obj;
lean_object* v_res_1533_;
v_res_1533_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v_msg_1518_, v___y_1519_, v___y_1520_);
stack->m_obj
 = v_res_1533_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg___boxed(lean_object* v_msg_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v_msg_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
return v_res_1538_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__3(void){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1543_ = lean_box(0);
v___x_1544_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1));
v___x_1545_ = l_Lean_mkConst(v___x_1544_, v___x_1543_);
return v___x_1545_;
}
}
static uint64_t _init_l_Lean_Server_registerRpcProcedure___closed__8(void){
_start:
{
lean_object* v___x_1565_; uint64_t v___x_1566_; 
v___x_1565_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__7));
v___x_1566_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1565_);
return v___x_1566_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__9(void){
_start:
{
uint64_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1567_ = lean_uint64_once(&l_Lean_Server_registerRpcProcedure___closed__8, &l_Lean_Server_registerRpcProcedure___closed__8_once, _init_l_Lean_Server_registerRpcProcedure___closed__8);
v___x_1568_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__7));
v___x_1569_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
lean_ctor_set_uint64(v___x_1569_, sizeof(void*)*1, v___x_1567_);
return v___x_1569_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__10(void){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_);
v___x_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
return v___x_1571_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__11(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1572_ = lean_box(1);
v___x_1573_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3);
v___x_1574_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__10, &l_Lean_Server_registerRpcProcedure___closed__10_once, _init_l_Lean_Server_registerRpcProcedure___closed__10);
v___x_1575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
lean_ctor_set(v___x_1575_, 1, v___x_1573_);
lean_ctor_set(v___x_1575_, 2, v___x_1572_);
return v___x_1575_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__12(void){
_start:
{
uint8_t v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1576_ = 1;
v___x_1577_ = lean_unsigned_to_nat(0u);
v___x_1578_ = lean_box(0);
v___x_1579_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__4));
v___x_1580_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__11, &l_Lean_Server_registerRpcProcedure___closed__11_once, _init_l_Lean_Server_registerRpcProcedure___closed__11);
v___x_1581_ = lean_box(1);
v___x_1582_ = 0;
v___x_1583_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__9, &l_Lean_Server_registerRpcProcedure___closed__9_once, _init_l_Lean_Server_registerRpcProcedure___closed__9);
v___x_1584_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
lean_ctor_set(v___x_1584_, 1, v___x_1581_);
lean_ctor_set(v___x_1584_, 2, v___x_1580_);
lean_ctor_set(v___x_1584_, 3, v___x_1579_);
lean_ctor_set(v___x_1584_, 4, v___x_1578_);
lean_ctor_set(v___x_1584_, 5, v___x_1577_);
lean_ctor_set(v___x_1584_, 6, v___x_1578_);
lean_ctor_set_uint8(v___x_1584_, sizeof(void*)*7, v___x_1582_);
lean_ctor_set_uint8(v___x_1584_, sizeof(void*)*7 + 1, v___x_1582_);
lean_ctor_set_uint8(v___x_1584_, sizeof(void*)*7 + 2, v___x_1582_);
lean_ctor_set_uint8(v___x_1584_, sizeof(void*)*7 + 3, v___x_1576_);
return v___x_1584_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__13(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1585_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1586_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__10, &l_Lean_Server_registerRpcProcedure___closed__10_once, _init_l_Lean_Server_registerRpcProcedure___closed__10);
v___x_1587_ = lean_unsigned_to_nat(0u);
v___x_1588_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
lean_ctor_set(v___x_1588_, 2, v___x_1587_);
lean_ctor_set(v___x_1588_, 3, v___x_1587_);
lean_ctor_set(v___x_1588_, 4, v___x_1586_);
lean_ctor_set(v___x_1588_, 5, v___x_1586_);
lean_ctor_set(v___x_1588_, 6, v___x_1586_);
lean_ctor_set(v___x_1588_, 7, v___x_1586_);
lean_ctor_set(v___x_1588_, 8, v___x_1586_);
lean_ctor_set(v___x_1588_, 9, v___x_1586_);
lean_ctor_set(v___x_1588_, 10, v___x_1586_);
lean_ctor_set(v___x_1588_, 11, v___x_1585_);
return v___x_1588_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__14(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__10, &l_Lean_Server_registerRpcProcedure___closed__10_once, _init_l_Lean_Server_registerRpcProcedure___closed__10);
v___x_1590_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
lean_ctor_set(v___x_1590_, 2, v___x_1589_);
lean_ctor_set(v___x_1590_, 3, v___x_1589_);
lean_ctor_set(v___x_1590_, 4, v___x_1589_);
lean_ctor_set(v___x_1590_, 5, v___x_1589_);
return v___x_1590_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__15(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__10, &l_Lean_Server_registerRpcProcedure___closed__10_once, _init_l_Lean_Server_registerRpcProcedure___closed__10);
v___x_1592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
lean_ctor_set(v___x_1592_, 2, v___x_1591_);
lean_ctor_set(v___x_1592_, 3, v___x_1591_);
lean_ctor_set(v___x_1592_, 4, v___x_1591_);
return v___x_1592_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__16(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1593_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__15, &l_Lean_Server_registerRpcProcedure___closed__15_once, _init_l_Lean_Server_registerRpcProcedure___closed__15);
v___x_1594_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3);
v___x_1595_ = lean_box(1);
v___x_1596_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__14, &l_Lean_Server_registerRpcProcedure___closed__14_once, _init_l_Lean_Server_registerRpcProcedure___closed__14);
v___x_1597_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__13, &l_Lean_Server_registerRpcProcedure___closed__13_once, _init_l_Lean_Server_registerRpcProcedure___closed__13);
v___x_1598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
lean_ctor_set(v___x_1598_, 1, v___x_1596_);
lean_ctor_set(v___x_1598_, 2, v___x_1595_);
lean_ctor_set(v___x_1598_, 3, v___x_1594_);
lean_ctor_set(v___x_1598_, 4, v___x_1593_);
return v___x_1598_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__17(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__10, &l_Lean_Server_registerRpcProcedure___closed__10_once, _init_l_Lean_Server_registerRpcProcedure___closed__10);
v___x_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
return v___x_1600_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__19(void){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__18));
v___x_1603_ = l_Lean_stringToMessageData(v___x_1602_);
return v___x_1603_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__20(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__3));
v___x_1605_ = l_Lean_stringToMessageData(v___x_1604_);
return v___x_1605_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__21(void){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__5));
v___x_1607_ = l_Lean_stringToMessageData(v___x_1606_);
return v___x_1607_;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__23(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__22));
v___x_1610_ = l_Lean_stringToMessageData(v___x_1609_);
return v___x_1610_;
}
}
lean_object* l_Lean_Server_registerRpcProcedure(lean_object* v_method_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v_env_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___x_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; 
v___x_1686_ = lean_box(0);
v___x_1687_ = lean_st_ref_get(v_a_1613_);
v_env_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc_ref(v_env_1688_);
lean_dec(v___x_1687_);
v___x_1689_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__19, &l_Lean_Server_registerRpcProcedure___closed__19_once, _init_l_Lean_Server_registerRpcProcedure___closed__19);
lean_inc(v_method_1611_);
v___x_1690_ = l_Lean_MessageData_ofName(v_method_1611_);
v___x_1691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1689_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__20, &l_Lean_Server_registerRpcProcedure___closed__20_once, _init_l_Lean_Server_registerRpcProcedure___closed__20);
v___x_1693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1691_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1704_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_1705_ = lean_st_ref_get(v___x_1704_);
v___x_1706_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(v___x_1705_, v_method_1611_);
lean_dec(v___x_1705_);
if (v___x_1706_ == 0)
{
v___y_1695_ = v_a_1612_;
v___y_1696_ = v_a_1613_;
goto v___jp_1694_;
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
lean_dec_ref(v_env_1688_);
lean_dec(v_method_1611_);
v___x_1707_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__23, &l_Lean_Server_registerRpcProcedure___closed__23_once, _init_l_Lean_Server_registerRpcProcedure___closed__23);
v___x_1708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1693_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
v___x_1709_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v___x_1708_, v_a_1612_, v_a_1613_);
return v___x_1709_;
}
v___jp_1615_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___f_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; uint8_t v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1618_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__2));
lean_inc_n(v_method_1611_, 2);
v___x_1619_ = l_Lean_Name_append(v_method_1611_, v___x_1618_);
v___x_1620_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_1621_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_));
v___x_1622_ = lean_box(0);
v___x_1623_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__3, &l_Lean_Server_registerRpcProcedure___closed__3_once, _init_l_Lean_Server_registerRpcProcedure___closed__3);
v___f_1624_ = lean_alloc_closure((void*)(l_Lean_Server_registerRpcProcedure___lam__1___boxed), 11, 4);
lean_closure_set(v___f_1624_, 0, v___x_1620_);
lean_closure_set(v___f_1624_, 1, v___x_1621_);
lean_closure_set(v___f_1624_, 2, v_method_1611_);
lean_closure_set(v___f_1624_, 3, v___x_1623_);
v___x_1625_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___boxed), 9, 2);
lean_closure_set(v___x_1625_, 0, lean_box(0));
lean_closure_set(v___x_1625_, 1, v___f_1624_);
v___x_1626_ = 1;
v___x_1627_ = 0;
v___x_1628_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__5));
v___x_1629_ = ((lean_object*)(l_Lean_Server_registerRpcProcedure___closed__6));
v___x_1630_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__12, &l_Lean_Server_registerRpcProcedure___closed__12_once, _init_l_Lean_Server_registerRpcProcedure___closed__12);
v___x_1631_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__16, &l_Lean_Server_registerRpcProcedure___closed__16_once, _init_l_Lean_Server_registerRpcProcedure___closed__16);
v___x_1632_ = lean_st_mk_ref(v___x_1631_);
v___x_1633_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_1625_, v___x_1628_, v___x_1629_, v___x_1630_, v___x_1632_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v_fst_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1676_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1633_, 1);
v_fst_1635_ = lean_ctor_get(v_a_1634_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_a_1634_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; 
v_unused_1677_ = lean_ctor_get(v_a_1634_, 1);
lean_dec(v_unused_1677_);
v___x_1637_ = v_a_1634_;
v_isShared_1638_ = v_isSharedCheck_1676_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_fst_1635_);
lean_dec(v_a_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1676_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; lean_object* v___x_1644_; 
v___x_1639_ = lean_st_ref_get(v___x_1632_);
lean_dec(v___x_1632_);
lean_dec(v___x_1639_);
lean_inc_n(v___x_1619_, 2);
v___x_1640_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1619_);
lean_ctor_set(v___x_1640_, 1, v___x_1622_);
lean_ctor_set(v___x_1640_, 2, v___x_1623_);
v___x_1641_ = lean_box(0);
v___x_1642_ = 1;
if (v_isShared_1638_ == 0)
{
lean_ctor_set_tag(v___x_1637_, 1);
lean_ctor_set(v___x_1637_, 1, v___x_1622_);
lean_ctor_set(v___x_1637_, 0, v___x_1619_);
v___x_1644_ = v___x_1637_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1619_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v___x_1622_);
v___x_1644_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1645_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1645_, 0, v___x_1640_);
lean_ctor_set(v___x_1645_, 1, v_fst_1635_);
lean_ctor_set(v___x_1645_, 2, v___x_1641_);
lean_ctor_set(v___x_1645_, 3, v___x_1644_);
lean_ctor_set_uint8(v___x_1645_, sizeof(void*)*4, v___x_1642_);
v___x_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
lean_inc_ref(v___x_1646_);
v___x_1647_ = l_Lean_addDecl(v___x_1646_, v___x_1627_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v___x_1648_; lean_object* v_env_1649_; lean_object* v_nextMacroScope_1650_; lean_object* v_ngen_1651_; lean_object* v_auxDeclNGen_1652_; lean_object* v_traceState_1653_; lean_object* v_recordedDeps_1654_; lean_object* v_messages_1655_; lean_object* v_infoState_1656_; lean_object* v_snapshotTasks_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1673_; 
lean_dec_ref_known(v___x_1647_, 1);
v___x_1648_ = lean_st_ref_take(v___y_1617_);
v_env_1649_ = lean_ctor_get(v___x_1648_, 0);
v_nextMacroScope_1650_ = lean_ctor_get(v___x_1648_, 1);
v_ngen_1651_ = lean_ctor_get(v___x_1648_, 2);
v_auxDeclNGen_1652_ = lean_ctor_get(v___x_1648_, 3);
v_traceState_1653_ = lean_ctor_get(v___x_1648_, 4);
v_recordedDeps_1654_ = lean_ctor_get(v___x_1648_, 6);
v_messages_1655_ = lean_ctor_get(v___x_1648_, 7);
v_infoState_1656_ = lean_ctor_get(v___x_1648_, 8);
v_snapshotTasks_1657_ = lean_ctor_get(v___x_1648_, 9);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1673_ == 0)
{
lean_object* v_unused_1674_; 
v_unused_1674_ = lean_ctor_get(v___x_1648_, 5);
lean_dec(v_unused_1674_);
v___x_1659_ = v___x_1648_;
v_isShared_1660_ = v_isSharedCheck_1673_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_snapshotTasks_1657_);
lean_inc(v_infoState_1656_);
lean_inc(v_messages_1655_);
lean_inc(v_recordedDeps_1654_);
lean_inc(v_traceState_1653_);
lean_inc(v_auxDeclNGen_1652_);
lean_inc(v_ngen_1651_);
lean_inc(v_nextMacroScope_1650_);
lean_inc(v_env_1649_);
lean_dec(v___x_1648_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1673_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1664_; 
lean_inc(v___x_1619_);
v___x_1661_ = l_Lean_markMeta(v_env_1649_, v___x_1619_);
v___x_1662_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__17, &l_Lean_Server_registerRpcProcedure___closed__17_once, _init_l_Lean_Server_registerRpcProcedure___closed__17);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 5, v___x_1662_);
lean_ctor_set(v___x_1659_, 0, v___x_1661_);
v___x_1664_ = v___x_1659_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_nextMacroScope_1650_);
lean_ctor_set(v_reuseFailAlloc_1672_, 2, v_ngen_1651_);
lean_ctor_set(v_reuseFailAlloc_1672_, 3, v_auxDeclNGen_1652_);
lean_ctor_set(v_reuseFailAlloc_1672_, 4, v_traceState_1653_);
lean_ctor_set(v_reuseFailAlloc_1672_, 5, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1672_, 6, v_recordedDeps_1654_);
lean_ctor_set(v_reuseFailAlloc_1672_, 7, v_messages_1655_);
lean_ctor_set(v_reuseFailAlloc_1672_, 8, v_infoState_1656_);
lean_ctor_set(v_reuseFailAlloc_1672_, 9, v_snapshotTasks_1657_);
v___x_1664_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = lean_st_ref_put(v___y_1617_, v___x_1664_);
v___x_1666_ = l_Lean_compileDecl(v___x_1646_, v___x_1626_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v___x_1667_; lean_object* v_env_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_dec_ref_known(v___x_1666_, 1);
v___x_1667_ = lean_st_ref_get(v___y_1617_);
v_env_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc_ref(v_env_1668_);
lean_dec(v___x_1667_);
v___x_1669_ = l_Lean_Server_userRpcProcedures;
v___x_1670_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1669_, v_env_1668_, v_method_1611_, v___x_1619_, v___x_1627_);
v___x_1671_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(v___x_1670_, v___y_1617_);
return v___x_1671_;
}
else
{
lean_dec(v___x_1619_);
lean_dec(v_method_1611_);
return v___x_1666_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1646_, 1);
lean_dec(v___x_1619_);
lean_dec(v_method_1611_);
return v___x_1647_;
}
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec(v___x_1632_);
lean_dec(v___x_1619_);
lean_dec(v_method_1611_);
v_a_1678_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1633_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1633_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
v___jp_1694_:
{
lean_object* v___x_1697_; lean_object* v_toEnvExtension_1698_; lean_object* v_asyncMode_1699_; uint8_t v___x_1700_; 
v___x_1697_ = l_Lean_Server_userRpcProcedures;
v_toEnvExtension_1698_ = lean_ctor_get(v___x_1697_, 0);
v_asyncMode_1699_ = lean_ctor_get(v_toEnvExtension_1698_, 2);
lean_inc(v_method_1611_);
v___x_1700_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_1686_, v___x_1697_, v_env_1688_, v_method_1611_, v_asyncMode_1699_);
if (v___x_1700_ == 0)
{
lean_dec_ref_known(v___x_1693_, 2);
v___y_1616_ = v___y_1695_;
v___y_1617_ = v___y_1696_;
goto v___jp_1615_;
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
lean_dec(v_method_1611_);
v___x_1701_ = lean_obj_once(&l_Lean_Server_registerRpcProcedure___closed__21, &l_Lean_Server_registerRpcProcedure___closed__21_once, _init_l_Lean_Server_registerRpcProcedure___closed__21);
v___x_1702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1693_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
v___x_1703_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v___x_1702_, v___y_1695_, v___y_1696_);
return v___x_1703_;
}
}
}
}
LEAN_EXPORT void l_Lean_Server_registerRpcProcedure_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_1611_ = stack[0].m_obj;
lean_object* v_a_1612_ = stack[1].m_obj;
lean_object* v_a_1613_ = stack[2].m_obj;
lean_object* v_res_1710_;
v_res_1710_ = l_Lean_Server_registerRpcProcedure(v_method_1611_, v_a_1612_, v_a_1613_);
stack->m_obj
 = v_res_1710_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___boxed(lean_object* v_method_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_Server_registerRpcProcedure(v_method_1711_, v_a_1712_, v_a_1713_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
return v_res_1715_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3(lean_object* v_00_u03b1_1716_, lean_object* v_msg_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v_msg_1717_, v___y_1718_, v___y_1719_);
return v___x_1721_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1717_ = stack[1].m_obj;
lean_object* v___y_1718_ = stack[2].m_obj;
lean_object* v___y_1719_ = stack[3].m_obj;
lean_object* v_res_1722_;
v_res_1722_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3(lean_box(0), v_msg_1717_, v___y_1718_, v___y_1719_);
stack->m_obj
 = v_res_1722_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___boxed(lean_object* v_00_u03b1_1723_, lean_object* v_msg_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3(v_00_u03b1_1723_, v_msg_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
return v_res_1728_;
}
}
lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(lean_object* v___x_1729_, lean_object* v_decl_1730_, lean_object* v_x_1731_, uint8_t v_attrKind_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v___x_1736_; 
lean_inc(v_decl_1730_);
v___x_1736_ = l_Lean_ensureAttrDeclIsMeta(v___x_1729_, v_decl_1730_, v_attrKind_1732_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v___x_1737_; 
lean_dec_ref_known(v___x_1736_, 1);
v___x_1737_ = l_Lean_Server_registerRpcProcedure(v_decl_1730_, v___y_1733_, v___y_1734_);
return v___x_1737_;
}
else
{
lean_dec(v_decl_1730_);
return v___x_1736_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1729_ = stack[0].m_obj;
lean_object* v_decl_1730_ = stack[1].m_obj;
lean_object* v_x_1731_ = stack[2].m_obj;
uint8_t v_attrKind_1732_ = stack[3].m_num;
lean_object* v___y_1733_ = stack[4].m_obj;
lean_object* v___y_1734_ = stack[5].m_obj;
lean_object* v_res_1738_;
v_res_1738_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(v___x_1729_, v_decl_1730_, v_x_1731_, v_attrKind_1732_, v___y_1733_, v___y_1734_);
stack->m_obj
 = v_res_1738_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed(lean_object* v___x_1739_, lean_object* v_decl_1740_, lean_object* v_x_1741_, lean_object* v_attrKind_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
uint8_t v_attrKind_boxed_1746_; lean_object* v_res_1747_; 
v_attrKind_boxed_1746_ = lean_unbox(v_attrKind_1742_);
v_res_1747_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(v___x_1739_, v_decl_1740_, v_x_1741_, v_attrKind_boxed_1746_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v_x_1741_);
return v_res_1747_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_));
v___x_1750_ = l_Lean_stringToMessageData(v___x_1749_);
return v___x_1750_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_));
v___x_1753_ = l_Lean_stringToMessageData(v___x_1752_);
return v___x_1753_;
}
}
lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(lean_object* v___x_1754_, lean_object* v_decl_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1759_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_);
v___x_1760_ = l_Lean_MessageData_ofName(v___x_1754_);
v___x_1761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1759_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = lean_obj_once(&l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_, &l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_);
v___x_1763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v___x_1763_, v___y_1756_, v___y_1757_);
return v___x_1764_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1754_ = stack[0].m_obj;
lean_object* v_decl_1755_ = stack[1].m_obj;
lean_object* v___y_1756_ = stack[2].m_obj;
lean_object* v___y_1757_ = stack[3].m_obj;
lean_object* v_res_1765_;
v_res_1765_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(v___x_1754_, v_decl_1755_, v___y_1756_, v___y_1757_);
stack->m_obj
 = v_res_1765_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed(lean_object* v___x_1766_, lean_object* v_decl_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(v___x_1766_, v_decl_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v_decl_1767_);
return v_res_1771_;
}
}
lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = ((lean_object*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__31_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_));
v___x_1852_ = l_Lean_registerBuiltinAttribute(v___x_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1853_;
v_res_1853_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1853_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed(lean_object* v_a_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_();
return v_res_1855_;
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
