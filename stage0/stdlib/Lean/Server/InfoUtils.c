// Lean compiler output
// Module: Lean.Server.InfoUtils
// Imports: public import Lean.DocString public import Lean.PrettyPrinter
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
lean_object* l_Lean_Elab_CompletionInfo_lctx(lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_Info_toElabInfo_x3f(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_getOptionDecls();
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_OptionDecl_fullDescr(lean_object*);
extern lean_object* l_Lean_errorExplanationExt;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ErrorExplanation_summaryWithSeverity(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppSignature(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_LocalContext_findFVar_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Elab_CompletionInfo_stx(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSyntheticSorry(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_List_filterMapTR_go___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_List_mapM_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_max_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTrailingSize(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "_private.Lean.Server.InfoUtils.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Server.InfoUtils"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1___closed__0_value;
static const lean_array_object l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodes___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodes___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodes(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfo___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoTree___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoTree(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Info_isTerm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_isTerm___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Info_isCompletion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_isCompletion___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_getCompletionInfos___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_getCompletionInfos___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_InfoTree_getCompletionInfos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_InfoTree_getCompletionInfos___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_InfoTree_getCompletionInfos___closed__0 = (const lean_object*)&l_Lean_Elab_InfoTree_getCompletionInfos___closed__0_value;
static const lean_array_object l_Lean_Elab_InfoTree_getCompletionInfos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_InfoTree_getCompletionInfos___closed__1 = (const lean_object*)&l_Lean_Elab_InfoTree_getCompletionInfos___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_getCompletionInfos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_stx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_stx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_lctx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_lctx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_pos_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_pos_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_tailPos_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_tailPos_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_range_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_range_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Info_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_contains___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_size_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_size_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Info_isSmaller(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_isSmaller___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_occursInside_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_occursInside_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Info_occursInOrOnBoundary(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_occursInOrOnBoundary___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__0(lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_InfoTree_smallestInfo_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_InfoTree_smallestInfo_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_instBEqHoverableInfoPrio_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instBEqHoverableInfoPrio_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_instBEqHoverableInfoPrio___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instBEqHoverableInfoPrio_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instBEqHoverableInfoPrio___closed__0 = (const lean_object*)&l_Lean_Elab_instBEqHoverableInfoPrio___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instBEqHoverableInfoPrio = (const lean_object*)&l_Lean_Elab_instBEqHoverableInfoPrio___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instOrdHoverableInfoPrio___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_instOrdHoverableInfoPrio___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instOrdHoverableInfoPrio___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instOrdHoverableInfoPrio___closed__0 = (const lean_object*)&l_Lean_Elab_instOrdHoverableInfoPrio___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instOrdHoverableInfoPrio = (const lean_object*)&l_Lean_Elab_instOrdHoverableInfoPrio___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_instLEHoverableInfoPrio;
LEAN_EXPORT lean_object* l_Lean_Elab_instMaxHoverableInfoPrio___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instMaxHoverableInfoPrio___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_instMaxHoverableInfoPrio___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instMaxHoverableInfoPrio___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instMaxHoverableInfoPrio___closed__0 = (const lean_object*)&l_Lean_Elab_instMaxHoverableInfoPrio___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instMaxHoverableInfoPrio = (const lean_object*)&l_Lean_Elab_instMaxHoverableInfoPrio___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__1_value;
static const lean_string_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__2_value;
static const lean_string_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__3_value;
static const lean_string_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__4_value;
static const lean_string_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "evalWithAnnotateState"};
static const lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(130, 32, 97, 238, 252, 41, 197, 171)}};
static const lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___closed__0 = (const lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__6(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__0_value;
static const lean_closure_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_type_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_type_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_docString_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_docString_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "*import "};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__0 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__0_value)}};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__1 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__2 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__2_value)}};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__3 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "```lean\n"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__0 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__0_value)}};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\n```"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__2 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__2_value)}};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__4 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__4_value)}};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Info_fmtHover_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\n***\n"};
static const lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Info_fmtHover_x3f___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Info_fmtHover_x3f___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Info_fmtHover_x3f___lam__1___closed__0_value)}};
static const lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Info_fmtHover_x3f___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Info_fmtHover_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Info_fmtHover_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Info_fmtHover_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__2 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__2_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__1 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__1_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__0 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value;
LEAN_EXPORT uint8_t l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_InfoTree_goalsAt_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_InfoTree_goalsAt_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_InfoTree_termGoalAt_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_InfoTree_termGoalAt_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__0(lean_object* v_toPure_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3_, 0, v_a_2_);
v___x_4_ = lean_apply_2(v_toPure_1_, lean_box(0), v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__2(lean_object* v_postNode_5_, lean_object* v_val_6_, lean_object* v_i_7_, lean_object* v_children_8_, lean_object* v_toBind_9_, lean_object* v___f_10_, lean_object* v_as_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_apply_4(v_postNode_5_, v_val_6_, v_i_7_, v_children_8_, v_as_11_);
v___x_13_ = lean_apply_4(v_toBind_9_, lean_box(0), lean_box(0), v___x_12_, v___f_10_);
return v___x_13_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_17_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__2));
v___x_18_ = lean_unsigned_to_nat(21u);
v___x_19_ = lean_unsigned_to_nat(65u);
v___x_20_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__1));
v___x_21_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__0));
v___x_22_ = l_mkPanicMessageWithDecl(v___x_21_, v___x_20_, v___x_19_, v___x_18_, v___x_17_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1___boxed(lean_object* v_postNode_23_, lean_object* v_val_24_, lean_object* v_i_25_, lean_object* v_children_26_, lean_object* v_toBind_27_, lean_object* v___f_28_, lean_object* v_x_29_, lean_object* v_inst_30_, lean_object* v_preNode_31_, lean_object* v___f_32_, lean_object* v_visitChildren_33_){
_start:
{
uint8_t v_visitChildren_boxed_34_; lean_object* v_res_35_; 
v_visitChildren_boxed_34_ = lean_unbox(v_visitChildren_33_);
v_res_35_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1(v_postNode_23_, v_val_24_, v_i_25_, v_children_26_, v_toBind_27_, v___f_28_, v_x_29_, v_inst_30_, v_preNode_31_, v___f_32_, v_visitChildren_boxed_34_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg(lean_object* v_inst_36_, lean_object* v_preNode_37_, lean_object* v_postNode_38_, lean_object* v_x_39_, lean_object* v_x_40_){
_start:
{
switch(lean_obj_tag(v_x_40_))
{
case 0:
{
lean_object* v_i_41_; lean_object* v_t_42_; lean_object* v___x_43_; 
v_i_41_ = lean_ctor_get(v_x_40_, 0);
lean_inc_ref(v_i_41_);
v_t_42_ = lean_ctor_get(v_x_40_, 1);
lean_inc_ref(v_t_42_);
lean_dec_ref(v_x_40_);
v___x_43_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_41_, v_x_39_);
v_x_39_ = v___x_43_;
v_x_40_ = v_t_42_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_39_) == 0)
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec_ref(v_x_40_);
lean_dec(v_postNode_38_);
lean_dec(v_preNode_37_);
v___x_45_ = lean_box(0);
v___x_46_ = l_instInhabitedOfMonad___redArg(v_inst_36_, v___x_45_);
v___x_47_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3);
v___x_48_ = l_panic___redArg(v___x_46_, v___x_47_);
lean_dec(v___x_46_);
return v___x_48_;
}
else
{
lean_object* v_toApplicative_49_; lean_object* v_toBind_50_; lean_object* v_toPure_51_; lean_object* v_i_52_; lean_object* v_children_53_; lean_object* v_val_54_; lean_object* v___f_55_; lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v_toApplicative_49_ = lean_ctor_get(v_inst_36_, 0);
v_toBind_50_ = lean_ctor_get(v_inst_36_, 1);
lean_inc_n(v_toBind_50_, 3);
v_toPure_51_ = lean_ctor_get(v_toApplicative_49_, 1);
v_i_52_ = lean_ctor_get(v_x_40_, 0);
lean_inc_ref_n(v_i_52_, 3);
v_children_53_ = lean_ctor_get(v_x_40_, 1);
lean_inc_ref_n(v_children_53_, 3);
lean_dec_ref(v_x_40_);
v_val_54_ = lean_ctor_get(v_x_39_, 0);
lean_inc_n(v_val_54_, 3);
lean_inc(v_toPure_51_);
v___f_55_ = lean_alloc_closure((void*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__0), 2, 1);
lean_closure_set(v___f_55_, 0, v_toPure_51_);
lean_inc_ref(v___f_55_);
lean_inc(v_postNode_38_);
v___f_56_ = lean_alloc_closure((void*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__2), 7, 6);
lean_closure_set(v___f_56_, 0, v_postNode_38_);
lean_closure_set(v___f_56_, 1, v_val_54_);
lean_closure_set(v___f_56_, 2, v_i_52_);
lean_closure_set(v___f_56_, 3, v_children_53_);
lean_closure_set(v___f_56_, 4, v_toBind_50_);
lean_closure_set(v___f_56_, 5, v___f_55_);
lean_inc(v_preNode_37_);
v___f_57_ = lean_alloc_closure((void*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1___boxed), 11, 10);
lean_closure_set(v___f_57_, 0, v_postNode_38_);
lean_closure_set(v___f_57_, 1, v_val_54_);
lean_closure_set(v___f_57_, 2, v_i_52_);
lean_closure_set(v___f_57_, 3, v_children_53_);
lean_closure_set(v___f_57_, 4, v_toBind_50_);
lean_closure_set(v___f_57_, 5, v___f_55_);
lean_closure_set(v___f_57_, 6, v_x_39_);
lean_closure_set(v___f_57_, 7, v_inst_36_);
lean_closure_set(v___f_57_, 8, v_preNode_37_);
lean_closure_set(v___f_57_, 9, v___f_56_);
v___x_58_ = lean_apply_3(v_preNode_37_, v_val_54_, v_i_52_, v_children_53_);
v___x_59_ = lean_apply_4(v_toBind_50_, lean_box(0), lean_box(0), v___x_58_, v___f_57_);
return v___x_59_;
}
}
default: 
{
lean_object* v_toApplicative_60_; lean_object* v_toPure_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v_toApplicative_60_ = lean_ctor_get(v_inst_36_, 0);
lean_inc_ref(v_toApplicative_60_);
lean_dec_ref(v_x_40_);
lean_dec(v_x_39_);
lean_dec(v_postNode_38_);
lean_dec(v_preNode_37_);
lean_dec_ref(v_inst_36_);
v_toPure_61_ = lean_ctor_get(v_toApplicative_60_, 1);
lean_inc(v_toPure_61_);
lean_dec_ref(v_toApplicative_60_);
v___x_62_ = lean_box(0);
v___x_63_ = lean_apply_2(v_toPure_61_, lean_box(0), v___x_62_);
return v___x_63_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1(lean_object* v_postNode_64_, lean_object* v_val_65_, lean_object* v_i_66_, lean_object* v_children_67_, lean_object* v_toBind_68_, lean_object* v___f_69_, lean_object* v_x_70_, lean_object* v_inst_71_, lean_object* v_preNode_72_, lean_object* v___f_73_, uint8_t v_visitChildren_74_){
_start:
{
if (v_visitChildren_74_ == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
lean_dec(v___f_73_);
lean_dec(v_preNode_72_);
lean_dec_ref(v_inst_71_);
lean_dec(v_x_70_);
v___x_75_ = lean_box(0);
v___x_76_ = lean_apply_4(v_postNode_64_, v_val_65_, v_i_66_, v_children_67_, v___x_75_);
v___x_77_ = lean_apply_4(v_toBind_68_, lean_box(0), lean_box(0), v___x_76_, v___f_69_);
return v___x_77_;
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec(v___f_69_);
lean_dec_ref(v_val_65_);
v___x_78_ = l_Lean_Elab_Info_updateContext_x3f(v_x_70_, v_i_66_);
lean_dec_ref(v_i_66_);
lean_inc_ref(v_inst_71_);
v___x_79_ = lean_alloc_closure((void*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg), 5, 4);
lean_closure_set(v___x_79_, 0, v_inst_71_);
lean_closure_set(v___x_79_, 1, v_preNode_72_);
lean_closure_set(v___x_79_, 2, v_postNode_64_);
lean_closure_set(v___x_79_, 3, v___x_78_);
v___x_80_ = l_Lean_PersistentArray_toList___redArg(v_children_67_);
lean_dec_ref(v_children_67_);
v___x_81_ = lean_box(0);
v___x_82_ = l_List_mapM_loop___redArg(v_inst_71_, v___x_79_, v___x_80_, v___x_81_);
v___x_83_ = lean_apply_4(v_toBind_68_, lean_box(0), lean_box(0), v___x_82_, v___f_73_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go(lean_object* v_m_84_, lean_object* v_00_u03b1_85_, lean_object* v_inst_86_, lean_object* v_preNode_87_, lean_object* v_postNode_88_, lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_86_, v_preNode_87_, v_postNode_88_, v_x_89_, v_x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM___redArg(lean_object* v_inst_92_, lean_object* v_preNode_93_, lean_object* v_postNode_94_, lean_object* v_ctx_x3f_95_, lean_object* v_x_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_92_, v_preNode_93_, v_postNode_94_, v_ctx_x3f_95_, v_x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM(lean_object* v_m_98_, lean_object* v_00_u03b1_99_, lean_object* v_inst_100_, lean_object* v_preNode_101_, lean_object* v_postNode_102_, lean_object* v_ctx_x3f_103_, lean_object* v_x_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_100_, v_preNode_101_, v_postNode_102_, v_ctx_x3f_103_, v_x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___redArg___lam__0(lean_object* v_postNode_106_, lean_object* v_ci_107_, lean_object* v_i_108_, lean_object* v_cs_109_, lean_object* v_x_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = lean_apply_3(v_postNode_106_, v_ci_107_, v_i_108_, v_cs_109_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___redArg___lam__0___boxed(lean_object* v_postNode_112_, lean_object* v_ci_113_, lean_object* v_i_114_, lean_object* v_cs_115_, lean_object* v_x_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Elab_InfoTree_visitM_x27___redArg___lam__0(v_postNode_112_, v_ci_113_, v_i_114_, v_cs_115_, v_x_116_);
lean_dec(v_x_116_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___redArg(lean_object* v_inst_118_, lean_object* v_preNode_119_, lean_object* v_postNode_120_, lean_object* v_ctx_x3f_121_, lean_object* v_t_122_){
_start:
{
lean_object* v_toApplicative_123_; lean_object* v_toFunctor_124_; lean_object* v_mapConst_125_; lean_object* v___f_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v_toApplicative_123_ = lean_ctor_get(v_inst_118_, 0);
v_toFunctor_124_ = lean_ctor_get(v_toApplicative_123_, 0);
v_mapConst_125_ = lean_ctor_get(v_toFunctor_124_, 1);
lean_inc(v_mapConst_125_);
v___f_126_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_126_, 0, v_postNode_120_);
v___x_127_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_118_, v_preNode_119_, v___f_126_, v_ctx_x3f_121_, v_t_122_);
v___x_128_ = lean_box(0);
v___x_129_ = lean_apply_4(v_mapConst_125_, lean_box(0), lean_box(0), v___x_128_, v___x_127_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27(lean_object* v_m_130_, lean_object* v_inst_131_, lean_object* v_preNode_132_, lean_object* v_postNode_133_, lean_object* v_ctx_x3f_134_, lean_object* v_t_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Elab_InfoTree_visitM_x27___redArg(v_inst_131_, v_preNode_132_, v_postNode_133_, v_ctx_x3f_134_, v_t_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__0(lean_object* v_x_137_){
_start:
{
if (lean_obj_tag(v_x_137_) == 0)
{
lean_object* v___x_138_; 
v___x_138_ = lean_box(0);
return v___x_138_;
}
else
{
lean_object* v_val_139_; 
v_val_139_ = lean_ctor_get(v_x_137_, 0);
lean_inc(v_val_139_);
return v_val_139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__0___boxed(lean_object* v_x_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__0(v_x_140_);
lean_dec(v_x_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1(lean_object* v_p_145_, lean_object* v_ci_146_, lean_object* v_i_147_, lean_object* v_cs_148_, lean_object* v_as_149_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_150_ = ((lean_object*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1___closed__0));
v___x_151_ = ((lean_object*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1___closed__1));
v___x_152_ = l_List_filterMapTR_go___redArg(v___x_150_, v_as_149_, v___x_151_);
v___x_153_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_150_, v___x_152_, v___x_151_);
v___x_154_ = lean_apply_4(v_p_145_, v_ci_146_, v_i_147_, v_cs_148_, v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__2(lean_object* v_toPure_155_, lean_object* v_x_156_, lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
uint8_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = 1;
v___x_160_ = lean_box(v___x_159_);
v___x_161_ = lean_apply_2(v_toPure_155_, lean_box(0), v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__2___boxed(lean_object* v_toPure_162_, lean_object* v_x_163_, lean_object* v_x_164_, lean_object* v_x_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__2(v_toPure_162_, v_x_163_, v_x_164_, v_x_165_);
lean_dec_ref(v_x_165_);
lean_dec_ref(v_x_164_);
lean_dec_ref(v_x_163_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg(lean_object* v_inst_168_, lean_object* v_p_169_, lean_object* v_i_170_){
_start:
{
lean_object* v_toApplicative_171_; lean_object* v_toFunctor_172_; lean_object* v_toPure_173_; lean_object* v_map_174_; lean_object* v___f_175_; lean_object* v___f_176_; lean_object* v___f_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_toApplicative_171_ = lean_ctor_get(v_inst_168_, 0);
v_toFunctor_172_ = lean_ctor_get(v_toApplicative_171_, 0);
v_toPure_173_ = lean_ctor_get(v_toApplicative_171_, 1);
v_map_174_ = lean_ctor_get(v_toFunctor_172_, 0);
lean_inc(v_map_174_);
v___f_175_ = ((lean_object*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___closed__0));
v___f_176_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1), 5, 1);
lean_closure_set(v___f_176_, 0, v_p_169_);
lean_inc(v_toPure_173_);
v___f_177_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__2___boxed), 4, 1);
lean_closure_set(v___f_177_, 0, v_toPure_173_);
v___x_178_ = lean_box(0);
v___x_179_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_168_, v___f_177_, v___f_176_, v___x_178_, v_i_170_);
v___x_180_ = lean_apply_4(v_map_174_, lean_box(0), lean_box(0), v___f_175_, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM(lean_object* v_m_181_, lean_object* v_00_u03b1_182_, lean_object* v_inst_183_, lean_object* v_p_184_, lean_object* v_i_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg(v_inst_183_, v_p_184_, v_i_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg___lam__0(lean_object* v_p_187_, lean_object* v_x1_188_, lean_object* v_x2_189_, lean_object* v_x3_190_, lean_object* v_x4_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_apply_4(v_p_187_, v_x1_188_, v_x2_189_, v_x3_190_, v_x4_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__1___redArg(lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
if (lean_obj_tag(v_a_193_) == 0)
{
lean_object* v___x_195_; 
v___x_195_ = lean_array_to_list(v_a_194_);
return v___x_195_;
}
else
{
lean_object* v_head_196_; lean_object* v_tail_197_; lean_object* v___x_198_; 
v_head_196_ = lean_ctor_get(v_a_193_, 0);
lean_inc(v_head_196_);
v_tail_197_ = lean_ctor_get(v_a_193_, 1);
lean_inc(v_tail_197_);
lean_dec_ref(v_a_193_);
v___x_198_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_194_, v_head_196_);
v_a_193_ = v_tail_197_;
v_a_194_ = v___x_198_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__0___redArg(lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
if (lean_obj_tag(v_a_200_) == 0)
{
lean_object* v___x_202_; 
v___x_202_ = lean_array_to_list(v_a_201_);
return v___x_202_;
}
else
{
lean_object* v_head_203_; 
v_head_203_ = lean_ctor_get(v_a_200_, 0);
if (lean_obj_tag(v_head_203_) == 0)
{
lean_object* v_tail_204_; 
v_tail_204_ = lean_ctor_get(v_a_200_, 1);
lean_inc(v_tail_204_);
lean_dec_ref(v_a_200_);
v_a_200_ = v_tail_204_;
goto _start;
}
else
{
lean_object* v_tail_206_; lean_object* v_val_207_; lean_object* v___x_208_; 
lean_inc_ref(v_head_203_);
v_tail_206_ = lean_ctor_get(v_a_200_, 1);
lean_inc(v_tail_206_);
lean_dec_ref(v_a_200_);
v_val_207_ = lean_ctor_get(v_head_203_, 0);
lean_inc(v_val_207_);
lean_dec_ref(v_head_203_);
v___x_208_ = lean_array_push(v_a_201_, v_val_207_);
v_a_200_ = v_tail_206_;
v_a_201_ = v___x_208_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__0(lean_object* v_p_210_, lean_object* v_ci_211_, lean_object* v_i_212_, lean_object* v_cs_213_, lean_object* v_as_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_215_ = ((lean_object*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1___closed__1));
v___x_216_ = l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__0___redArg(v_as_214_, v___x_215_);
v___x_217_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__1___redArg(v___x_216_, v___x_215_);
v___x_218_ = lean_apply_4(v_p_210_, v_ci_211_, v_i_212_, v_cs_213_, v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg(lean_object* v_msg_226_){
_start:
{
lean_object* v___f_227_; lean_object* v___f_228_; lean_object* v___f_229_; lean_object* v___f_230_; lean_object* v___f_231_; lean_object* v___f_232_; lean_object* v___f_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___f_227_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__0));
v___f_228_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__1));
v___f_229_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__2));
v___f_230_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__3));
v___f_231_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__4));
v___f_232_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__5));
v___f_233_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__6));
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v___f_227_);
lean_ctor_set(v___x_234_, 1, v___f_228_);
v___x_235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___f_229_);
lean_ctor_set(v___x_235_, 2, v___f_230_);
lean_ctor_set(v___x_235_, 3, v___f_231_);
lean_ctor_set(v___x_235_, 4, v___f_232_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v___f_233_);
v___x_237_ = lean_box(0);
v___x_238_ = l_instInhabitedOfMonad___redArg(v___x_236_, v___x_237_);
v___x_239_ = lean_panic_fn_borrowed(v___x_238_, v_msg_226_);
lean_dec(v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(lean_object* v_preNode_240_, lean_object* v_postNode_241_, lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
switch(lean_obj_tag(v_x_243_))
{
case 0:
{
lean_object* v_i_244_; lean_object* v_t_245_; lean_object* v___x_246_; 
v_i_244_ = lean_ctor_get(v_x_243_, 0);
lean_inc_ref(v_i_244_);
v_t_245_ = lean_ctor_get(v_x_243_, 1);
lean_inc_ref(v_t_245_);
lean_dec_ref(v_x_243_);
v___x_246_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_244_, v_x_242_);
v_x_242_ = v___x_246_;
v_x_243_ = v_t_245_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_242_) == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec_ref(v_x_243_);
lean_dec(v_postNode_241_);
lean_dec_ref(v_preNode_240_);
v___x_248_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3);
v___x_249_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg(v___x_248_);
return v___x_249_;
}
else
{
lean_object* v_i_250_; lean_object* v_children_251_; lean_object* v_val_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v_i_250_ = lean_ctor_get(v_x_243_, 0);
lean_inc_ref_n(v_i_250_, 2);
v_children_251_ = lean_ctor_get(v_x_243_, 1);
lean_inc_ref_n(v_children_251_, 2);
lean_dec_ref(v_x_243_);
v_val_252_ = lean_ctor_get(v_x_242_, 0);
lean_inc_n(v_val_252_, 2);
lean_inc_ref(v_preNode_240_);
v___x_253_ = lean_apply_3(v_preNode_240_, v_val_252_, v_i_250_, v_children_251_);
v___x_254_ = lean_unbox(v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_263_; 
lean_dec_ref(v_preNode_240_);
v_isSharedCheck_263_ = !lean_is_exclusive(v_x_242_);
if (v_isSharedCheck_263_ == 0)
{
lean_object* v_unused_264_; 
v_unused_264_ = lean_ctor_get(v_x_242_, 0);
lean_dec(v_unused_264_);
v___x_256_ = v_x_242_;
v_isShared_257_ = v_isSharedCheck_263_;
goto v_resetjp_255_;
}
else
{
lean_dec(v_x_242_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_263_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_258_ = lean_box(0);
v___x_259_ = lean_apply_4(v_postNode_241_, v_val_252_, v_i_250_, v_children_251_, v___x_258_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 0, v___x_259_);
v___x_261_ = v___x_256_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_265_ = l_Lean_Elab_Info_updateContext_x3f(v_x_242_, v_i_250_);
v___x_266_ = l_Lean_PersistentArray_toList___redArg(v_children_251_);
v___x_267_ = lean_box(0);
lean_inc(v_postNode_241_);
v___x_268_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4___redArg(v_preNode_240_, v_postNode_241_, v___x_265_, v___x_266_, v___x_267_);
v___x_269_ = lean_apply_4(v_postNode_241_, v_val_252_, v_i_250_, v_children_251_, v___x_268_);
v___x_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
}
}
default: 
{
lean_object* v___x_271_; 
lean_dec_ref(v_x_243_);
lean_dec(v_x_242_);
lean_dec(v_postNode_241_);
lean_dec_ref(v_preNode_240_);
v___x_271_ = lean_box(0);
return v___x_271_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4___redArg(lean_object* v_preNode_272_, lean_object* v_postNode_273_, lean_object* v___x_274_, lean_object* v_x_275_, lean_object* v_x_276_){
_start:
{
if (lean_obj_tag(v_x_275_) == 0)
{
lean_object* v___x_277_; 
lean_dec(v___x_274_);
lean_dec(v_postNode_273_);
lean_dec_ref(v_preNode_272_);
v___x_277_ = l_List_reverse___redArg(v_x_276_);
return v___x_277_;
}
else
{
lean_object* v_head_278_; lean_object* v_tail_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_288_; 
v_head_278_ = lean_ctor_get(v_x_275_, 0);
v_tail_279_ = lean_ctor_get(v_x_275_, 1);
v_isSharedCheck_288_ = !lean_is_exclusive(v_x_275_);
if (v_isSharedCheck_288_ == 0)
{
v___x_281_ = v_x_275_;
v_isShared_282_ = v_isSharedCheck_288_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_tail_279_);
lean_inc(v_head_278_);
lean_dec(v_x_275_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_288_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_285_; 
lean_inc(v___x_274_);
lean_inc(v_postNode_273_);
lean_inc_ref(v_preNode_272_);
v___x_283_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v_preNode_272_, v_postNode_273_, v___x_274_, v_head_278_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 1, v_x_276_);
lean_ctor_set(v___x_281_, 0, v___x_283_);
v___x_285_ = v___x_281_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_x_276_);
v___x_285_ = v_reuseFailAlloc_287_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
v_x_275_ = v_tail_279_;
v_x_276_ = v___x_285_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__1(lean_object* v_x_289_, lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
uint8_t v___x_292_; 
v___x_292_ = 1;
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__1___boxed(lean_object* v_x_293_, lean_object* v_x_294_, lean_object* v_x_295_){
_start:
{
uint8_t v_res_296_; lean_object* v_r_297_; 
v_res_296_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__1(v_x_293_, v_x_294_, v_x_295_);
lean_dec_ref(v_x_295_);
lean_dec_ref(v_x_294_);
lean_dec_ref(v_x_293_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg(lean_object* v_p_299_, lean_object* v_i_300_){
_start:
{
lean_object* v___f_301_; lean_object* v___f_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___f_301_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__0), 5, 1);
lean_closure_set(v___f_301_, 0, v_p_299_);
v___f_302_ = ((lean_object*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___closed__0));
v___x_303_ = lean_box(0);
v___x_304_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v___f_302_, v___f_301_, v___x_303_, v_i_300_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v___x_305_; 
v___x_305_ = lean_box(0);
return v___x_305_;
}
else
{
lean_object* v_val_306_; 
v_val_306_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_val_306_);
lean_dec_ref(v___x_304_);
return v_val_306_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg(lean_object* v_p_307_, lean_object* v_i_308_){
_start:
{
lean_object* v___f_309_; lean_object* v___x_310_; 
v___f_309_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg___lam__0), 5, 1);
lean_closure_set(v___f_309_, 0, v_p_307_);
v___x_310_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg(v___f_309_, v_i_308_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUp(lean_object* v_00_u03b1_311_, lean_object* v_p_312_, lean_object* v_i_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg(v_p_312_, v_i_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0(lean_object* v_00_u03b1_315_, lean_object* v_p_316_, lean_object* v_i_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg(v_p_316_, v_i_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__0(lean_object* v_00_u03b1_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__0___redArg(v_a_320_, v_a_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__1(lean_object* v_00_u03b1_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__1___redArg(v_a_324_, v_a_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_327_, lean_object* v_msg_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg(v_msg_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2(lean_object* v_00_u03b1_330_, lean_object* v_preNode_331_, lean_object* v_postNode_332_, lean_object* v_x_333_, lean_object* v_x_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v_preNode_331_, v_postNode_332_, v_x_333_, v_x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_336_, lean_object* v_preNode_337_, lean_object* v_postNode_338_, lean_object* v___x_339_, lean_object* v_x_340_, lean_object* v_x_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4___redArg(v_preNode_337_, v_postNode_338_, v___x_339_, v_x_340_, v_x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0(lean_object* v_inst_343_, lean_object* v_____do__lift_344_){
_start:
{
if (lean_obj_tag(v_____do__lift_344_) == 0)
{
lean_object* v_toApplicative_345_; lean_object* v_toPure_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_toApplicative_345_ = lean_ctor_get(v_inst_343_, 0);
lean_inc_ref(v_toApplicative_345_);
lean_dec_ref(v_inst_343_);
v_toPure_346_ = lean_ctor_get(v_toApplicative_345_, 1);
lean_inc(v_toPure_346_);
lean_dec_ref(v_toApplicative_345_);
v___x_347_ = lean_box(0);
v___x_348_ = lean_apply_2(v_toPure_346_, lean_box(0), v___x_347_);
return v___x_348_;
}
else
{
lean_object* v_toApplicative_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_360_; 
v_toApplicative_349_ = lean_ctor_get(v_inst_343_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v_inst_343_);
if (v_isSharedCheck_360_ == 0)
{
lean_object* v_unused_361_; 
v_unused_361_ = lean_ctor_get(v_inst_343_, 1);
lean_dec(v_unused_361_);
v___x_351_ = v_inst_343_;
v_isShared_352_ = v_isSharedCheck_360_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_toApplicative_349_);
lean_dec(v_inst_343_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_360_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v_val_353_; lean_object* v_toPure_354_; lean_object* v___x_355_; lean_object* v___x_357_; 
v_val_353_ = lean_ctor_get(v_____do__lift_344_, 0);
v_toPure_354_ = lean_ctor_get(v_toApplicative_349_, 1);
lean_inc(v_toPure_354_);
lean_dec_ref(v_toApplicative_349_);
v___x_355_ = lean_box(0);
lean_inc(v_val_353_);
if (v_isShared_352_ == 0)
{
lean_ctor_set_tag(v___x_351_, 1);
lean_ctor_set(v___x_351_, 1, v___x_355_);
lean_ctor_set(v___x_351_, 0, v_val_353_);
v___x_357_ = v___x_351_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_val_353_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v___x_355_);
v___x_357_ = v_reuseFailAlloc_359_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; 
v___x_358_ = lean_apply_2(v_toPure_354_, lean_box(0), v___x_357_);
return v___x_358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0___boxed(lean_object* v_inst_362_, lean_object* v_____do__lift_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0(v_inst_362_, v_____do__lift_363_);
lean_dec(v_____do__lift_363_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__1(lean_object* v_inst_365_, lean_object* v_p_366_, lean_object* v___f_367_, lean_object* v_ctx_368_, lean_object* v_i_369_, lean_object* v_cs_370_, lean_object* v_rs_371_){
_start:
{
uint8_t v___x_372_; 
v___x_372_ = l_List_isEmpty___redArg(v_rs_371_);
if (v___x_372_ == 0)
{
lean_object* v_toApplicative_373_; lean_object* v_toPure_374_; lean_object* v___x_375_; 
lean_dec_ref(v_cs_370_);
lean_dec_ref(v_i_369_);
lean_dec_ref(v_ctx_368_);
lean_dec(v___f_367_);
lean_dec(v_p_366_);
v_toApplicative_373_ = lean_ctor_get(v_inst_365_, 0);
lean_inc_ref(v_toApplicative_373_);
lean_dec_ref(v_inst_365_);
v_toPure_374_ = lean_ctor_get(v_toApplicative_373_, 1);
lean_inc(v_toPure_374_);
lean_dec_ref(v_toApplicative_373_);
v___x_375_ = lean_apply_2(v_toPure_374_, lean_box(0), v_rs_371_);
return v___x_375_;
}
else
{
lean_object* v_toBind_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
lean_dec(v_rs_371_);
v_toBind_376_ = lean_ctor_get(v_inst_365_, 1);
lean_inc(v_toBind_376_);
lean_dec_ref(v_inst_365_);
v___x_377_ = lean_apply_3(v_p_366_, v_ctx_368_, v_i_369_, v_cs_370_);
v___x_378_ = lean_apply_4(v_toBind_376_, lean_box(0), lean_box(0), v___x_377_, v___f_367_);
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg(lean_object* v_inst_379_, lean_object* v_p_380_, lean_object* v_infoTree_381_){
_start:
{
lean_object* v___f_382_; lean_object* v___f_383_; lean_object* v___x_384_; 
lean_inc_ref_n(v_inst_379_, 2);
v___f_382_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_382_, 0, v_inst_379_);
v___f_383_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__1), 7, 3);
lean_closure_set(v___f_383_, 0, v_inst_379_);
lean_closure_set(v___f_383_, 1, v_p_380_);
lean_closure_set(v___f_383_, 2, v___f_382_);
v___x_384_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg(v_inst_379_, v___f_383_, v_infoTree_381_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM(lean_object* v_m_385_, lean_object* v_00_u03b1_386_, lean_object* v_inst_387_, lean_object* v_p_388_, lean_object* v_infoTree_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Elab_InfoTree_deepestNodesM___redArg(v_inst_387_, v_p_388_, v_infoTree_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodes___redArg___lam__0(lean_object* v_p_391_, lean_object* v_x1_392_, lean_object* v_x2_393_, lean_object* v_x3_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = lean_apply_3(v_p_391_, v_x1_392_, v_x2_393_, v_x3_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0(lean_object* v_p_396_, lean_object* v_ctx_397_, lean_object* v_i_398_, lean_object* v_cs_399_, lean_object* v_rs_400_){
_start:
{
uint8_t v___x_401_; 
v___x_401_ = l_List_isEmpty___redArg(v_rs_400_);
if (v___x_401_ == 0)
{
lean_dec_ref(v_cs_399_);
lean_dec_ref(v_i_398_);
lean_dec_ref(v_ctx_397_);
lean_dec_ref(v_p_396_);
lean_inc(v_rs_400_);
return v_rs_400_;
}
else
{
lean_object* v___x_402_; 
v___x_402_ = lean_apply_3(v_p_396_, v_ctx_397_, v_i_398_, v_cs_399_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v___x_403_; 
v___x_403_ = lean_box(0);
return v___x_403_;
}
else
{
lean_object* v_val_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_val_404_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_val_404_);
lean_dec_ref(v___x_402_);
v___x_405_ = lean_box(0);
v___x_406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_406_, 0, v_val_404_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
return v___x_406_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0___boxed(lean_object* v_p_407_, lean_object* v_ctx_408_, lean_object* v_i_409_, lean_object* v_cs_410_, lean_object* v_rs_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0(v_p_407_, v_ctx_408_, v_i_409_, v_cs_410_, v_rs_411_);
lean_dec(v_rs_411_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg(lean_object* v_p_413_, lean_object* v_infoTree_414_){
_start:
{
lean_object* v___f_415_; lean_object* v___x_416_; 
v___f_415_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_415_, 0, v_p_413_);
v___x_416_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg(v___f_415_, v_infoTree_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodes___redArg(lean_object* v_p_417_, lean_object* v_infoTree_418_){
_start:
{
lean_object* v___f_419_; lean_object* v___x_420_; 
v___f_419_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_deepestNodes___redArg___lam__0), 4, 1);
lean_closure_set(v___f_419_, 0, v_p_417_);
v___x_420_ = l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg(v___f_419_, v_infoTree_418_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodes(lean_object* v_00_u03b1_421_, lean_object* v_p_422_, lean_object* v_infoTree_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v_p_422_, v_infoTree_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0(lean_object* v_00_u03b1_425_, lean_object* v_p_426_, lean_object* v_infoTree_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg(v_p_426_, v_infoTree_427_);
return v___x_428_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(lean_object* v_f_430_, lean_object* v___x_431_, lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
if (lean_obj_tag(v_x_432_) == 0)
{
lean_object* v_cs_434_; lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v_cs_434_ = lean_ctor_get(v_x_432_, 0);
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = lean_array_get_size(v_cs_434_);
v___x_437_ = lean_nat_dec_lt(v___x_435_, v___x_436_);
if (v___x_437_ == 0)
{
lean_dec(v___x_431_);
lean_dec(v_f_430_);
return v_x_433_;
}
else
{
uint8_t v___x_438_; 
v___x_438_ = lean_nat_dec_le(v___x_436_, v___x_436_);
if (v___x_438_ == 0)
{
if (v___x_437_ == 0)
{
lean_dec(v___x_431_);
lean_dec(v_f_430_);
return v_x_433_;
}
else
{
size_t v___x_439_; size_t v___x_440_; lean_object* v___x_441_; 
v___x_439_ = ((size_t)0ULL);
v___x_440_ = lean_usize_of_nat(v___x_436_);
v___x_441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_430_, v___x_431_, v_cs_434_, v___x_439_, v___x_440_, v_x_433_);
return v___x_441_;
}
}
else
{
size_t v___x_442_; size_t v___x_443_; lean_object* v___x_444_; 
v___x_442_ = ((size_t)0ULL);
v___x_443_ = lean_usize_of_nat(v___x_436_);
v___x_444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_430_, v___x_431_, v_cs_434_, v___x_442_, v___x_443_, v_x_433_);
return v___x_444_;
}
}
}
else
{
lean_object* v_vs_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v_vs_445_ = lean_ctor_get(v_x_432_, 0);
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = lean_array_get_size(v_vs_445_);
v___x_448_ = lean_nat_dec_lt(v___x_446_, v___x_447_);
if (v___x_448_ == 0)
{
lean_dec(v___x_431_);
lean_dec(v_f_430_);
return v_x_433_;
}
else
{
uint8_t v___x_449_; 
v___x_449_ = lean_nat_dec_le(v___x_447_, v___x_447_);
if (v___x_449_ == 0)
{
if (v___x_448_ == 0)
{
lean_dec(v___x_431_);
lean_dec(v_f_430_);
return v_x_433_;
}
else
{
size_t v___x_450_; size_t v___x_451_; lean_object* v___x_452_; 
v___x_450_ = ((size_t)0ULL);
v___x_451_ = lean_usize_of_nat(v___x_447_);
v___x_452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_430_, v___x_431_, v_vs_445_, v___x_450_, v___x_451_, v_x_433_);
return v___x_452_;
}
}
else
{
size_t v___x_453_; size_t v___x_454_; lean_object* v___x_455_; 
v___x_453_ = ((size_t)0ULL);
v___x_454_ = lean_usize_of_nat(v___x_447_);
v___x_455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_430_, v___x_431_, v_vs_445_, v___x_453_, v___x_454_, v_x_433_);
return v___x_455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(lean_object* v_f_456_, lean_object* v___x_457_, lean_object* v_as_458_, size_t v_i_459_, size_t v_stop_460_, lean_object* v_b_461_){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = lean_usize_dec_eq(v_i_459_, v_stop_460_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; size_t v___x_465_; size_t v___x_466_; 
v___x_463_ = lean_array_uget_borrowed(v_as_458_, v_i_459_);
lean_inc(v___x_457_);
lean_inc(v_f_456_);
v___x_464_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(v_f_456_, v___x_457_, v___x_463_, v_b_461_);
v___x_465_ = ((size_t)1ULL);
v___x_466_ = lean_usize_add(v_i_459_, v___x_465_);
v_i_459_ = v___x_466_;
v_b_461_ = v___x_464_;
goto _start;
}
else
{
lean_dec(v___x_457_);
lean_dec(v_f_456_);
return v_b_461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(lean_object* v_f_468_, lean_object* v___x_469_, lean_object* v_x_470_, size_t v_x_471_, size_t v_x_472_, lean_object* v_x_473_){
_start:
{
if (lean_obj_tag(v_x_470_) == 0)
{
lean_object* v_cs_474_; lean_object* v___x_475_; size_t v___x_476_; lean_object* v_j_477_; lean_object* v___x_478_; size_t v___x_479_; size_t v___x_480_; size_t v___x_481_; size_t v___x_482_; size_t v___x_483_; size_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_cs_474_ = lean_ctor_get(v_x_470_, 0);
v___x_475_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0);
v___x_476_ = lean_usize_shift_right(v_x_471_, v_x_472_);
v_j_477_ = lean_usize_to_nat(v___x_476_);
v___x_478_ = lean_array_get_borrowed(v___x_475_, v_cs_474_, v_j_477_);
v___x_479_ = ((size_t)1ULL);
v___x_480_ = lean_usize_shift_left(v___x_479_, v_x_472_);
v___x_481_ = lean_usize_sub(v___x_480_, v___x_479_);
v___x_482_ = lean_usize_land(v_x_471_, v___x_481_);
v___x_483_ = ((size_t)5ULL);
v___x_484_ = lean_usize_sub(v_x_472_, v___x_483_);
lean_inc(v___x_469_);
lean_inc(v_f_468_);
v___x_485_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(v_f_468_, v___x_469_, v___x_478_, v___x_482_, v___x_484_, v_x_473_);
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_nat_add(v_j_477_, v___x_486_);
lean_dec(v_j_477_);
v___x_488_ = lean_array_get_size(v_cs_474_);
v___x_489_ = lean_nat_dec_lt(v___x_487_, v___x_488_);
if (v___x_489_ == 0)
{
lean_dec(v___x_487_);
lean_dec(v___x_469_);
lean_dec(v_f_468_);
return v___x_485_;
}
else
{
uint8_t v___x_490_; 
v___x_490_ = lean_nat_dec_le(v___x_488_, v___x_488_);
if (v___x_490_ == 0)
{
if (v___x_489_ == 0)
{
lean_dec(v___x_487_);
lean_dec(v___x_469_);
lean_dec(v_f_468_);
return v___x_485_;
}
else
{
size_t v___x_491_; size_t v___x_492_; lean_object* v___x_493_; 
v___x_491_ = lean_usize_of_nat(v___x_487_);
lean_dec(v___x_487_);
v___x_492_ = lean_usize_of_nat(v___x_488_);
v___x_493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_468_, v___x_469_, v_cs_474_, v___x_491_, v___x_492_, v___x_485_);
return v___x_493_;
}
}
else
{
size_t v___x_494_; size_t v___x_495_; lean_object* v___x_496_; 
v___x_494_ = lean_usize_of_nat(v___x_487_);
lean_dec(v___x_487_);
v___x_495_ = lean_usize_of_nat(v___x_488_);
v___x_496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_468_, v___x_469_, v_cs_474_, v___x_494_, v___x_495_, v___x_485_);
return v___x_496_;
}
}
}
else
{
lean_object* v_vs_497_; lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v_vs_497_ = lean_ctor_get(v_x_470_, 0);
v___x_498_ = lean_usize_to_nat(v_x_471_);
v___x_499_ = lean_array_get_size(v_vs_497_);
v___x_500_ = lean_nat_dec_lt(v___x_498_, v___x_499_);
if (v___x_500_ == 0)
{
lean_dec(v___x_498_);
lean_dec(v___x_469_);
lean_dec(v_f_468_);
return v_x_473_;
}
else
{
uint8_t v___x_501_; 
v___x_501_ = lean_nat_dec_le(v___x_499_, v___x_499_);
if (v___x_501_ == 0)
{
if (v___x_500_ == 0)
{
lean_dec(v___x_498_);
lean_dec(v___x_469_);
lean_dec(v_f_468_);
return v_x_473_;
}
else
{
size_t v___x_502_; size_t v___x_503_; lean_object* v___x_504_; 
v___x_502_ = lean_usize_of_nat(v___x_498_);
lean_dec(v___x_498_);
v___x_503_ = lean_usize_of_nat(v___x_499_);
v___x_504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_468_, v___x_469_, v_vs_497_, v___x_502_, v___x_503_, v_x_473_);
return v___x_504_;
}
}
else
{
size_t v___x_505_; size_t v___x_506_; lean_object* v___x_507_; 
v___x_505_ = lean_usize_of_nat(v___x_498_);
lean_dec(v___x_498_);
v___x_506_ = lean_usize_of_nat(v___x_499_);
v___x_507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_468_, v___x_469_, v_vs_497_, v___x_505_, v___x_506_, v_x_473_);
return v___x_507_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(lean_object* v_f_508_, lean_object* v___x_509_, lean_object* v_t_510_, lean_object* v_init_511_, lean_object* v_start_512_){
_start:
{
lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = lean_nat_dec_eq(v_start_512_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v_root_515_; lean_object* v_tail_516_; size_t v_shift_517_; lean_object* v_tailOff_518_; uint8_t v___x_519_; 
v_root_515_ = lean_ctor_get(v_t_510_, 0);
v_tail_516_ = lean_ctor_get(v_t_510_, 1);
v_shift_517_ = lean_ctor_get_usize(v_t_510_, 4);
v_tailOff_518_ = lean_ctor_get(v_t_510_, 3);
v___x_519_ = lean_nat_dec_le(v_tailOff_518_, v_start_512_);
if (v___x_519_ == 0)
{
size_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_520_ = lean_usize_of_nat(v_start_512_);
lean_inc(v___x_509_);
lean_inc(v_f_508_);
v___x_521_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(v_f_508_, v___x_509_, v_root_515_, v___x_520_, v_shift_517_, v_init_511_);
v___x_522_ = lean_array_get_size(v_tail_516_);
v___x_523_ = lean_nat_dec_lt(v___x_513_, v___x_522_);
if (v___x_523_ == 0)
{
lean_dec(v___x_509_);
lean_dec(v_f_508_);
return v___x_521_;
}
else
{
uint8_t v___x_524_; 
v___x_524_ = lean_nat_dec_le(v___x_522_, v___x_522_);
if (v___x_524_ == 0)
{
if (v___x_523_ == 0)
{
lean_dec(v___x_509_);
lean_dec(v_f_508_);
return v___x_521_;
}
else
{
size_t v___x_525_; size_t v___x_526_; lean_object* v___x_527_; 
v___x_525_ = ((size_t)0ULL);
v___x_526_ = lean_usize_of_nat(v___x_522_);
v___x_527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_508_, v___x_509_, v_tail_516_, v___x_525_, v___x_526_, v___x_521_);
return v___x_527_;
}
}
else
{
size_t v___x_528_; size_t v___x_529_; lean_object* v___x_530_; 
v___x_528_ = ((size_t)0ULL);
v___x_529_ = lean_usize_of_nat(v___x_522_);
v___x_530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_508_, v___x_509_, v_tail_516_, v___x_528_, v___x_529_, v___x_521_);
return v___x_530_;
}
}
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_531_ = lean_nat_sub(v_start_512_, v_tailOff_518_);
v___x_532_ = lean_array_get_size(v_tail_516_);
v___x_533_ = lean_nat_dec_lt(v___x_531_, v___x_532_);
if (v___x_533_ == 0)
{
lean_dec(v___x_531_);
lean_dec(v___x_509_);
lean_dec(v_f_508_);
return v_init_511_;
}
else
{
uint8_t v___x_534_; 
v___x_534_ = lean_nat_dec_le(v___x_532_, v___x_532_);
if (v___x_534_ == 0)
{
if (v___x_533_ == 0)
{
lean_dec(v___x_531_);
lean_dec(v___x_509_);
lean_dec(v_f_508_);
return v_init_511_;
}
else
{
size_t v___x_535_; size_t v___x_536_; lean_object* v___x_537_; 
v___x_535_ = lean_usize_of_nat(v___x_531_);
lean_dec(v___x_531_);
v___x_536_ = lean_usize_of_nat(v___x_532_);
v___x_537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_508_, v___x_509_, v_tail_516_, v___x_535_, v___x_536_, v_init_511_);
return v___x_537_;
}
}
else
{
size_t v___x_538_; size_t v___x_539_; lean_object* v___x_540_; 
v___x_538_ = lean_usize_of_nat(v___x_531_);
lean_dec(v___x_531_);
v___x_539_ = lean_usize_of_nat(v___x_532_);
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_508_, v___x_509_, v_tail_516_, v___x_538_, v___x_539_, v_init_511_);
return v___x_540_;
}
}
}
}
else
{
lean_object* v_root_541_; lean_object* v_tail_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v_root_541_ = lean_ctor_get(v_t_510_, 0);
v_tail_542_ = lean_ctor_get(v_t_510_, 1);
lean_inc(v___x_509_);
lean_inc(v_f_508_);
v___x_543_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(v_f_508_, v___x_509_, v_root_541_, v_init_511_);
v___x_544_ = lean_array_get_size(v_tail_542_);
v___x_545_ = lean_nat_dec_lt(v___x_513_, v___x_544_);
if (v___x_545_ == 0)
{
lean_dec(v___x_509_);
lean_dec(v_f_508_);
return v___x_543_;
}
else
{
uint8_t v___x_546_; 
v___x_546_ = lean_nat_dec_le(v___x_544_, v___x_544_);
if (v___x_546_ == 0)
{
if (v___x_545_ == 0)
{
lean_dec(v___x_509_);
lean_dec(v_f_508_);
return v___x_543_;
}
else
{
size_t v___x_547_; size_t v___x_548_; lean_object* v___x_549_; 
v___x_547_ = ((size_t)0ULL);
v___x_548_ = lean_usize_of_nat(v___x_544_);
v___x_549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_508_, v___x_509_, v_tail_542_, v___x_547_, v___x_548_, v___x_543_);
return v___x_549_;
}
}
else
{
size_t v___x_550_; size_t v___x_551_; lean_object* v___x_552_; 
v___x_550_ = ((size_t)0ULL);
v___x_551_ = lean_usize_of_nat(v___x_544_);
v___x_552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_508_, v___x_509_, v_tail_542_, v___x_550_, v___x_551_, v___x_543_);
return v___x_552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go___redArg(lean_object* v_f_553_, lean_object* v_ctx_x3f_554_, lean_object* v_a_555_, lean_object* v_x_556_){
_start:
{
switch(lean_obj_tag(v_x_556_))
{
case 0:
{
lean_object* v_i_557_; lean_object* v_t_558_; lean_object* v___x_559_; 
v_i_557_ = lean_ctor_get(v_x_556_, 0);
lean_inc_ref(v_i_557_);
v_t_558_ = lean_ctor_get(v_x_556_, 1);
lean_inc_ref(v_t_558_);
lean_dec_ref(v_x_556_);
v___x_559_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_557_, v_ctx_x3f_554_);
v_ctx_x3f_554_ = v___x_559_;
v_x_556_ = v_t_558_;
goto _start;
}
case 1:
{
lean_object* v_i_561_; lean_object* v_children_562_; lean_object* v___y_564_; 
v_i_561_ = lean_ctor_get(v_x_556_, 0);
lean_inc_ref(v_i_561_);
v_children_562_ = lean_ctor_get(v_x_556_, 1);
lean_inc_ref(v_children_562_);
lean_dec_ref(v_x_556_);
if (lean_obj_tag(v_ctx_x3f_554_) == 0)
{
v___y_564_ = v_a_555_;
goto v___jp_563_;
}
else
{
lean_object* v_val_568_; lean_object* v___x_569_; 
v_val_568_ = lean_ctor_get(v_ctx_x3f_554_, 0);
lean_inc(v_f_553_);
lean_inc_ref(v_i_561_);
lean_inc(v_val_568_);
v___x_569_ = lean_apply_3(v_f_553_, v_val_568_, v_i_561_, v_a_555_);
v___y_564_ = v___x_569_;
goto v___jp_563_;
}
v___jp_563_:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_565_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_554_, v_i_561_);
lean_dec_ref(v_i_561_);
v___x_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(v_f_553_, v___x_565_, v_children_562_, v___y_564_, v___x_566_);
lean_dec_ref(v_children_562_);
return v___x_567_;
}
}
default: 
{
lean_dec_ref(v_x_556_);
lean_dec(v_ctx_x3f_554_);
lean_dec(v_f_553_);
return v_a_555_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(lean_object* v_f_570_, lean_object* v___x_571_, lean_object* v_as_572_, size_t v_i_573_, size_t v_stop_574_, lean_object* v_b_575_){
_start:
{
uint8_t v___x_576_; 
v___x_576_ = lean_usize_dec_eq(v_i_573_, v_stop_574_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; size_t v___x_579_; size_t v___x_580_; 
v___x_577_ = lean_array_uget_borrowed(v_as_572_, v_i_573_);
lean_inc(v___x_577_);
lean_inc(v___x_571_);
lean_inc(v_f_570_);
v___x_578_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go___redArg(v_f_570_, v___x_571_, v_b_575_, v___x_577_);
v___x_579_ = ((size_t)1ULL);
v___x_580_ = lean_usize_add(v_i_573_, v___x_579_);
v_i_573_ = v___x_580_;
v_b_575_ = v___x_578_;
goto _start;
}
else
{
lean_dec(v___x_571_);
lean_dec(v_f_570_);
return v_b_575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg___boxed(lean_object* v_f_582_, lean_object* v___x_583_, lean_object* v_as_584_, lean_object* v_i_585_, lean_object* v_stop_586_, lean_object* v_b_587_){
_start:
{
size_t v_i_boxed_588_; size_t v_stop_boxed_589_; lean_object* v_res_590_; 
v_i_boxed_588_ = lean_unbox_usize(v_i_585_);
lean_dec(v_i_585_);
v_stop_boxed_589_ = lean_unbox_usize(v_stop_586_);
lean_dec(v_stop_586_);
v_res_590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_582_, v___x_583_, v_as_584_, v_i_boxed_588_, v_stop_boxed_589_, v_b_587_);
lean_dec_ref(v_as_584_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_591_, lean_object* v___x_592_, lean_object* v_as_593_, lean_object* v_i_594_, lean_object* v_stop_595_, lean_object* v_b_596_){
_start:
{
size_t v_i_boxed_597_; size_t v_stop_boxed_598_; lean_object* v_res_599_; 
v_i_boxed_597_ = lean_unbox_usize(v_i_594_);
lean_dec(v_i_594_);
v_stop_boxed_598_ = lean_unbox_usize(v_stop_595_);
lean_dec(v_stop_595_);
v_res_599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_591_, v___x_592_, v_as_593_, v_i_boxed_597_, v_stop_boxed_598_, v_b_596_);
lean_dec_ref(v_as_593_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg___boxed(lean_object* v_f_600_, lean_object* v___x_601_, lean_object* v_x_602_, lean_object* v_x_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(v_f_600_, v___x_601_, v_x_602_, v_x_603_);
lean_dec_ref(v_x_602_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___boxed(lean_object* v_f_605_, lean_object* v___x_606_, lean_object* v_x_607_, lean_object* v_x_608_, lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
size_t v_x_1543__boxed_611_; size_t v_x_1544__boxed_612_; lean_object* v_res_613_; 
v_x_1543__boxed_611_ = lean_unbox_usize(v_x_608_);
lean_dec(v_x_608_);
v_x_1544__boxed_612_ = lean_unbox_usize(v_x_609_);
lean_dec(v_x_609_);
v_res_613_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(v_f_605_, v___x_606_, v_x_607_, v_x_1543__boxed_611_, v_x_1544__boxed_612_, v_x_610_);
lean_dec_ref(v_x_607_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg___boxed(lean_object* v_f_614_, lean_object* v___x_615_, lean_object* v_t_616_, lean_object* v_init_617_, lean_object* v_start_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(v_f_614_, v___x_615_, v_t_616_, v_init_617_, v_start_618_);
lean_dec(v_start_618_);
lean_dec_ref(v_t_616_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go(lean_object* v_00_u03b1_620_, lean_object* v_f_621_, lean_object* v_ctx_x3f_622_, lean_object* v_a_623_, lean_object* v_x_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go___redArg(v_f_621_, v_ctx_x3f_622_, v_a_623_, v_x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0(lean_object* v_00_u03b1_626_, lean_object* v_f_627_, lean_object* v___x_628_, lean_object* v_t_629_, lean_object* v_init_630_, lean_object* v_start_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(v_f_627_, v___x_628_, v_t_629_, v_init_630_, v_start_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___boxed(lean_object* v_00_u03b1_633_, lean_object* v_f_634_, lean_object* v___x_635_, lean_object* v_t_636_, lean_object* v_init_637_, lean_object* v_start_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0(v_00_u03b1_633_, v_f_634_, v___x_635_, v_t_636_, v_init_637_, v_start_638_);
lean_dec(v_start_638_);
lean_dec_ref(v_t_636_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0(lean_object* v_00_u03b1_640_, lean_object* v_f_641_, lean_object* v___x_642_, lean_object* v_x_643_, size_t v_x_644_, size_t v_x_645_, lean_object* v_x_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(v_f_641_, v___x_642_, v_x_643_, v_x_644_, v_x_645_, v_x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_648_, lean_object* v_f_649_, lean_object* v___x_650_, lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_x_654_){
_start:
{
size_t v_x_1763__boxed_655_; size_t v_x_1764__boxed_656_; lean_object* v_res_657_; 
v_x_1763__boxed_655_ = lean_unbox_usize(v_x_652_);
lean_dec(v_x_652_);
v_x_1764__boxed_656_ = lean_unbox_usize(v_x_653_);
lean_dec(v_x_653_);
v_res_657_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0(v_00_u03b1_648_, v_f_649_, v___x_650_, v_x_651_, v_x_1763__boxed_655_, v_x_1764__boxed_656_, v_x_654_);
lean_dec_ref(v_x_651_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1(lean_object* v_00_u03b1_658_, lean_object* v_f_659_, lean_object* v___x_660_, lean_object* v_as_661_, size_t v_i_662_, size_t v_stop_663_, lean_object* v_b_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_659_, v___x_660_, v_as_661_, v_i_662_, v_stop_663_, v_b_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___boxed(lean_object* v_00_u03b1_666_, lean_object* v_f_667_, lean_object* v___x_668_, lean_object* v_as_669_, lean_object* v_i_670_, lean_object* v_stop_671_, lean_object* v_b_672_){
_start:
{
size_t v_i_boxed_673_; size_t v_stop_boxed_674_; lean_object* v_res_675_; 
v_i_boxed_673_ = lean_unbox_usize(v_i_670_);
lean_dec(v_i_670_);
v_stop_boxed_674_ = lean_unbox_usize(v_stop_671_);
lean_dec(v_stop_671_);
v_res_675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1(v_00_u03b1_666_, v_f_667_, v___x_668_, v_as_669_, v_i_boxed_673_, v_stop_boxed_674_, v_b_672_);
lean_dec_ref(v_as_669_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2(lean_object* v_00_u03b1_676_, lean_object* v_f_677_, lean_object* v___x_678_, lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(v_f_677_, v___x_678_, v_x_679_, v_x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___boxed(lean_object* v_00_u03b1_682_, lean_object* v_f_683_, lean_object* v___x_684_, lean_object* v_x_685_, lean_object* v_x_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2(v_00_u03b1_682_, v_f_683_, v___x_684_, v_x_685_, v_x_686_);
lean_dec_ref(v_x_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_688_, lean_object* v_f_689_, lean_object* v___x_690_, lean_object* v_as_691_, size_t v_i_692_, size_t v_stop_693_, lean_object* v_b_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_689_, v___x_690_, v_as_691_, v_i_692_, v_stop_693_, v_b_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_696_, lean_object* v_f_697_, lean_object* v___x_698_, lean_object* v_as_699_, lean_object* v_i_700_, lean_object* v_stop_701_, lean_object* v_b_702_){
_start:
{
size_t v_i_boxed_703_; size_t v_stop_boxed_704_; lean_object* v_res_705_; 
v_i_boxed_703_ = lean_unbox_usize(v_i_700_);
lean_dec(v_i_700_);
v_stop_boxed_704_ = lean_unbox_usize(v_stop_701_);
lean_dec(v_stop_701_);
v_res_705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1(v_00_u03b1_696_, v_f_697_, v___x_698_, v_as_699_, v_i_boxed_703_, v_stop_boxed_704_, v_b_702_);
lean_dec_ref(v_as_699_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfo___redArg(lean_object* v_f_706_, lean_object* v_init_707_, lean_object* v_x_708_){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = lean_box(0);
v___x_710_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go___redArg(v_f_706_, v___x_709_, v_init_707_, v_x_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfo(lean_object* v_00_u03b1_711_, lean_object* v_f_712_, lean_object* v_init_713_, lean_object* v_x_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v_f_712_, v_init_713_, v_x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__1(lean_object* v___f_716_, lean_object* v_a_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = lean_apply_1(v___f_716_, v_a_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0___boxed(lean_object* v_ctx_x3f_719_, lean_object* v_i_720_, lean_object* v_inst_721_, lean_object* v_f_722_, lean_object* v_children_723_, lean_object* v_a_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0(v_ctx_x3f_719_, v_i_720_, v_inst_721_, v_f_722_, v_children_723_, v_a_724_);
lean_dec_ref(v_i_720_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg(lean_object* v_inst_726_, lean_object* v_f_727_, lean_object* v_ctx_x3f_728_, lean_object* v_a_729_, lean_object* v_x_730_){
_start:
{
switch(lean_obj_tag(v_x_730_))
{
case 0:
{
lean_object* v_i_731_; lean_object* v_t_732_; lean_object* v___x_733_; 
v_i_731_ = lean_ctor_get(v_x_730_, 0);
lean_inc_ref(v_i_731_);
v_t_732_ = lean_ctor_get(v_x_730_, 1);
lean_inc_ref(v_t_732_);
lean_dec_ref(v_x_730_);
v___x_733_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_731_, v_ctx_x3f_728_);
v_ctx_x3f_728_ = v___x_733_;
v_x_730_ = v_t_732_;
goto _start;
}
case 1:
{
lean_object* v_toApplicative_735_; lean_object* v_toBind_736_; lean_object* v_toPure_737_; lean_object* v_i_738_; lean_object* v_children_739_; lean_object* v___f_740_; 
v_toApplicative_735_ = lean_ctor_get(v_inst_726_, 0);
v_toBind_736_ = lean_ctor_get(v_inst_726_, 1);
lean_inc(v_toBind_736_);
v_toPure_737_ = lean_ctor_get(v_toApplicative_735_, 1);
lean_inc(v_toPure_737_);
v_i_738_ = lean_ctor_get(v_x_730_, 0);
lean_inc_ref_n(v_i_738_, 2);
v_children_739_ = lean_ctor_get(v_x_730_, 1);
lean_inc_ref(v_children_739_);
lean_dec_ref(v_x_730_);
lean_inc(v_f_727_);
lean_inc(v_ctx_x3f_728_);
v___f_740_ = lean_alloc_closure((void*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_740_, 0, v_ctx_x3f_728_);
lean_closure_set(v___f_740_, 1, v_i_738_);
lean_closure_set(v___f_740_, 2, v_inst_726_);
lean_closure_set(v___f_740_, 3, v_f_727_);
lean_closure_set(v___f_740_, 4, v_children_739_);
if (lean_obj_tag(v_ctx_x3f_728_) == 0)
{
lean_object* v___f_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
lean_dec_ref(v_i_738_);
lean_dec(v_f_727_);
v___f_741_ = lean_alloc_closure((void*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__1), 2, 1);
lean_closure_set(v___f_741_, 0, v___f_740_);
v___x_742_ = lean_apply_2(v_toPure_737_, lean_box(0), v_a_729_);
v___x_743_ = lean_apply_4(v_toBind_736_, lean_box(0), lean_box(0), v___x_742_, v___f_741_);
return v___x_743_;
}
else
{
lean_object* v_val_744_; lean_object* v___f_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec(v_toPure_737_);
v_val_744_ = lean_ctor_get(v_ctx_x3f_728_, 0);
lean_inc(v_val_744_);
lean_dec_ref(v_ctx_x3f_728_);
v___f_745_ = lean_alloc_closure((void*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__1), 2, 1);
lean_closure_set(v___f_745_, 0, v___f_740_);
v___x_746_ = lean_apply_3(v_f_727_, v_val_744_, v_i_738_, v_a_729_);
v___x_747_ = lean_apply_4(v_toBind_736_, lean_box(0), lean_box(0), v___x_746_, v___f_745_);
return v___x_747_;
}
}
default: 
{
lean_object* v_toApplicative_748_; lean_object* v_toPure_749_; lean_object* v___x_750_; 
v_toApplicative_748_ = lean_ctor_get(v_inst_726_, 0);
lean_inc_ref(v_toApplicative_748_);
lean_dec_ref(v_x_730_);
lean_dec(v_ctx_x3f_728_);
lean_dec(v_f_727_);
lean_dec_ref(v_inst_726_);
v_toPure_749_ = lean_ctor_get(v_toApplicative_748_, 1);
lean_inc(v_toPure_749_);
lean_dec_ref(v_toApplicative_748_);
v___x_750_ = lean_apply_2(v_toPure_749_, lean_box(0), v_a_729_);
return v___x_750_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0(lean_object* v_ctx_x3f_751_, lean_object* v_i_752_, lean_object* v_inst_753_, lean_object* v_f_754_, lean_object* v_children_755_, lean_object* v_a_756_){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_757_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_751_, v_i_752_);
lean_inc_ref(v_inst_753_);
v___x_758_ = lean_alloc_closure((void*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg), 5, 3);
lean_closure_set(v___x_758_, 0, v_inst_753_);
lean_closure_set(v___x_758_, 1, v_f_754_);
lean_closure_set(v___x_758_, 2, v___x_757_);
v___x_759_ = lean_unsigned_to_nat(0u);
v___x_760_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_753_, v_children_755_, v___x_758_, v_a_756_, v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go(lean_object* v_m_761_, lean_object* v_00_u03b1_762_, lean_object* v_inst_763_, lean_object* v_f_764_, lean_object* v_ctx_x3f_765_, lean_object* v_a_766_, lean_object* v_x_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg(v_inst_763_, v_f_764_, v_ctx_x3f_765_, v_a_766_, v_x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___redArg(lean_object* v_inst_769_, lean_object* v_f_770_, lean_object* v_init_771_, lean_object* v_x_772_){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_box(0);
v___x_774_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg(v_inst_769_, v_f_770_, v___x_773_, v_init_771_, v_x_772_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM(lean_object* v_m_775_, lean_object* v_00_u03b1_776_, lean_object* v_inst_777_, lean_object* v_f_778_, lean_object* v_init_779_, lean_object* v_x_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_Elab_InfoTree_foldInfoM___redArg(v_inst_777_, v_f_778_, v_init_779_, v_x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(lean_object* v_f_782_, lean_object* v___x_783_, lean_object* v_x_784_, lean_object* v_x_785_){
_start:
{
if (lean_obj_tag(v_x_784_) == 0)
{
lean_object* v_cs_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_cs_786_ = lean_ctor_get(v_x_784_, 0);
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_788_ = lean_array_get_size(v_cs_786_);
v___x_789_ = lean_nat_dec_lt(v___x_787_, v___x_788_);
if (v___x_789_ == 0)
{
lean_dec(v___x_783_);
lean_dec(v_f_782_);
return v_x_785_;
}
else
{
uint8_t v___x_790_; 
v___x_790_ = lean_nat_dec_le(v___x_788_, v___x_788_);
if (v___x_790_ == 0)
{
if (v___x_789_ == 0)
{
lean_dec(v___x_783_);
lean_dec(v_f_782_);
return v_x_785_;
}
else
{
size_t v___x_791_; size_t v___x_792_; lean_object* v___x_793_; 
v___x_791_ = ((size_t)0ULL);
v___x_792_ = lean_usize_of_nat(v___x_788_);
v___x_793_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_782_, v___x_783_, v_cs_786_, v___x_791_, v___x_792_, v_x_785_);
return v___x_793_;
}
}
else
{
size_t v___x_794_; size_t v___x_795_; lean_object* v___x_796_; 
v___x_794_ = ((size_t)0ULL);
v___x_795_ = lean_usize_of_nat(v___x_788_);
v___x_796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_782_, v___x_783_, v_cs_786_, v___x_794_, v___x_795_, v_x_785_);
return v___x_796_;
}
}
}
else
{
lean_object* v_vs_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v_vs_797_ = lean_ctor_get(v_x_784_, 0);
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = lean_array_get_size(v_vs_797_);
v___x_800_ = lean_nat_dec_lt(v___x_798_, v___x_799_);
if (v___x_800_ == 0)
{
lean_dec(v___x_783_);
lean_dec(v_f_782_);
return v_x_785_;
}
else
{
uint8_t v___x_801_; 
v___x_801_ = lean_nat_dec_le(v___x_799_, v___x_799_);
if (v___x_801_ == 0)
{
if (v___x_800_ == 0)
{
lean_dec(v___x_783_);
lean_dec(v_f_782_);
return v_x_785_;
}
else
{
size_t v___x_802_; size_t v___x_803_; lean_object* v___x_804_; 
v___x_802_ = ((size_t)0ULL);
v___x_803_ = lean_usize_of_nat(v___x_799_);
v___x_804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_782_, v___x_783_, v_vs_797_, v___x_802_, v___x_803_, v_x_785_);
return v___x_804_;
}
}
else
{
size_t v___x_805_; size_t v___x_806_; lean_object* v___x_807_; 
v___x_805_ = ((size_t)0ULL);
v___x_806_ = lean_usize_of_nat(v___x_799_);
v___x_807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_782_, v___x_783_, v_vs_797_, v___x_805_, v___x_806_, v_x_785_);
return v___x_807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(lean_object* v_f_808_, lean_object* v___x_809_, lean_object* v_as_810_, size_t v_i_811_, size_t v_stop_812_, lean_object* v_b_813_){
_start:
{
uint8_t v___x_814_; 
v___x_814_ = lean_usize_dec_eq(v_i_811_, v_stop_812_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v___x_816_; size_t v___x_817_; size_t v___x_818_; 
v___x_815_ = lean_array_uget_borrowed(v_as_810_, v_i_811_);
lean_inc(v___x_809_);
lean_inc(v_f_808_);
v___x_816_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(v_f_808_, v___x_809_, v___x_815_, v_b_813_);
v___x_817_ = ((size_t)1ULL);
v___x_818_ = lean_usize_add(v_i_811_, v___x_817_);
v_i_811_ = v___x_818_;
v_b_813_ = v___x_816_;
goto _start;
}
else
{
lean_dec(v___x_809_);
lean_dec(v_f_808_);
return v_b_813_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(lean_object* v_f_820_, lean_object* v___x_821_, lean_object* v_x_822_, size_t v_x_823_, size_t v_x_824_, lean_object* v_x_825_){
_start:
{
if (lean_obj_tag(v_x_822_) == 0)
{
lean_object* v_cs_826_; lean_object* v___x_827_; size_t v___x_828_; lean_object* v_j_829_; lean_object* v___x_830_; size_t v___x_831_; size_t v___x_832_; size_t v___x_833_; size_t v___x_834_; size_t v___x_835_; size_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v_cs_826_ = lean_ctor_get(v_x_822_, 0);
v___x_827_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0);
v___x_828_ = lean_usize_shift_right(v_x_823_, v_x_824_);
v_j_829_ = lean_usize_to_nat(v___x_828_);
v___x_830_ = lean_array_get_borrowed(v___x_827_, v_cs_826_, v_j_829_);
v___x_831_ = ((size_t)1ULL);
v___x_832_ = lean_usize_shift_left(v___x_831_, v_x_824_);
v___x_833_ = lean_usize_sub(v___x_832_, v___x_831_);
v___x_834_ = lean_usize_land(v_x_823_, v___x_833_);
v___x_835_ = ((size_t)5ULL);
v___x_836_ = lean_usize_sub(v_x_824_, v___x_835_);
lean_inc(v___x_821_);
lean_inc(v_f_820_);
v___x_837_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(v_f_820_, v___x_821_, v___x_830_, v___x_834_, v___x_836_, v_x_825_);
v___x_838_ = lean_unsigned_to_nat(1u);
v___x_839_ = lean_nat_add(v_j_829_, v___x_838_);
lean_dec(v_j_829_);
v___x_840_ = lean_array_get_size(v_cs_826_);
v___x_841_ = lean_nat_dec_lt(v___x_839_, v___x_840_);
if (v___x_841_ == 0)
{
lean_dec(v___x_839_);
lean_dec(v___x_821_);
lean_dec(v_f_820_);
return v___x_837_;
}
else
{
uint8_t v___x_842_; 
v___x_842_ = lean_nat_dec_le(v___x_840_, v___x_840_);
if (v___x_842_ == 0)
{
if (v___x_841_ == 0)
{
lean_dec(v___x_839_);
lean_dec(v___x_821_);
lean_dec(v_f_820_);
return v___x_837_;
}
else
{
size_t v___x_843_; size_t v___x_844_; lean_object* v___x_845_; 
v___x_843_ = lean_usize_of_nat(v___x_839_);
lean_dec(v___x_839_);
v___x_844_ = lean_usize_of_nat(v___x_840_);
v___x_845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_820_, v___x_821_, v_cs_826_, v___x_843_, v___x_844_, v___x_837_);
return v___x_845_;
}
}
else
{
size_t v___x_846_; size_t v___x_847_; lean_object* v___x_848_; 
v___x_846_ = lean_usize_of_nat(v___x_839_);
lean_dec(v___x_839_);
v___x_847_ = lean_usize_of_nat(v___x_840_);
v___x_848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_820_, v___x_821_, v_cs_826_, v___x_846_, v___x_847_, v___x_837_);
return v___x_848_;
}
}
}
else
{
lean_object* v_vs_849_; lean_object* v___x_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v_vs_849_ = lean_ctor_get(v_x_822_, 0);
v___x_850_ = lean_usize_to_nat(v_x_823_);
v___x_851_ = lean_array_get_size(v_vs_849_);
v___x_852_ = lean_nat_dec_lt(v___x_850_, v___x_851_);
if (v___x_852_ == 0)
{
lean_dec(v___x_850_);
lean_dec(v___x_821_);
lean_dec(v_f_820_);
return v_x_825_;
}
else
{
uint8_t v___x_853_; 
v___x_853_ = lean_nat_dec_le(v___x_851_, v___x_851_);
if (v___x_853_ == 0)
{
if (v___x_852_ == 0)
{
lean_dec(v___x_850_);
lean_dec(v___x_821_);
lean_dec(v_f_820_);
return v_x_825_;
}
else
{
size_t v___x_854_; size_t v___x_855_; lean_object* v___x_856_; 
v___x_854_ = lean_usize_of_nat(v___x_850_);
lean_dec(v___x_850_);
v___x_855_ = lean_usize_of_nat(v___x_851_);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_820_, v___x_821_, v_vs_849_, v___x_854_, v___x_855_, v_x_825_);
return v___x_856_;
}
}
else
{
size_t v___x_857_; size_t v___x_858_; lean_object* v___x_859_; 
v___x_857_ = lean_usize_of_nat(v___x_850_);
lean_dec(v___x_850_);
v___x_858_ = lean_usize_of_nat(v___x_851_);
v___x_859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_820_, v___x_821_, v_vs_849_, v___x_857_, v___x_858_, v_x_825_);
return v___x_859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(lean_object* v_f_860_, lean_object* v___x_861_, lean_object* v_t_862_, lean_object* v_init_863_, lean_object* v_start_864_){
_start:
{
lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_865_ = lean_unsigned_to_nat(0u);
v___x_866_ = lean_nat_dec_eq(v_start_864_, v___x_865_);
if (v___x_866_ == 0)
{
lean_object* v_root_867_; lean_object* v_tail_868_; size_t v_shift_869_; lean_object* v_tailOff_870_; uint8_t v___x_871_; 
v_root_867_ = lean_ctor_get(v_t_862_, 0);
v_tail_868_ = lean_ctor_get(v_t_862_, 1);
v_shift_869_ = lean_ctor_get_usize(v_t_862_, 4);
v_tailOff_870_ = lean_ctor_get(v_t_862_, 3);
v___x_871_ = lean_nat_dec_le(v_tailOff_870_, v_start_864_);
if (v___x_871_ == 0)
{
size_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_872_ = lean_usize_of_nat(v_start_864_);
lean_inc(v___x_861_);
lean_inc(v_f_860_);
v___x_873_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(v_f_860_, v___x_861_, v_root_867_, v___x_872_, v_shift_869_, v_init_863_);
v___x_874_ = lean_array_get_size(v_tail_868_);
v___x_875_ = lean_nat_dec_lt(v___x_865_, v___x_874_);
if (v___x_875_ == 0)
{
lean_dec(v___x_861_);
lean_dec(v_f_860_);
return v___x_873_;
}
else
{
uint8_t v___x_876_; 
v___x_876_ = lean_nat_dec_le(v___x_874_, v___x_874_);
if (v___x_876_ == 0)
{
if (v___x_875_ == 0)
{
lean_dec(v___x_861_);
lean_dec(v_f_860_);
return v___x_873_;
}
else
{
size_t v___x_877_; size_t v___x_878_; lean_object* v___x_879_; 
v___x_877_ = ((size_t)0ULL);
v___x_878_ = lean_usize_of_nat(v___x_874_);
v___x_879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_860_, v___x_861_, v_tail_868_, v___x_877_, v___x_878_, v___x_873_);
return v___x_879_;
}
}
else
{
size_t v___x_880_; size_t v___x_881_; lean_object* v___x_882_; 
v___x_880_ = ((size_t)0ULL);
v___x_881_ = lean_usize_of_nat(v___x_874_);
v___x_882_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_860_, v___x_861_, v_tail_868_, v___x_880_, v___x_881_, v___x_873_);
return v___x_882_;
}
}
}
else
{
lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v___x_883_ = lean_nat_sub(v_start_864_, v_tailOff_870_);
v___x_884_ = lean_array_get_size(v_tail_868_);
v___x_885_ = lean_nat_dec_lt(v___x_883_, v___x_884_);
if (v___x_885_ == 0)
{
lean_dec(v___x_883_);
lean_dec(v___x_861_);
lean_dec(v_f_860_);
return v_init_863_;
}
else
{
uint8_t v___x_886_; 
v___x_886_ = lean_nat_dec_le(v___x_884_, v___x_884_);
if (v___x_886_ == 0)
{
if (v___x_885_ == 0)
{
lean_dec(v___x_883_);
lean_dec(v___x_861_);
lean_dec(v_f_860_);
return v_init_863_;
}
else
{
size_t v___x_887_; size_t v___x_888_; lean_object* v___x_889_; 
v___x_887_ = lean_usize_of_nat(v___x_883_);
lean_dec(v___x_883_);
v___x_888_ = lean_usize_of_nat(v___x_884_);
v___x_889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_860_, v___x_861_, v_tail_868_, v___x_887_, v___x_888_, v_init_863_);
return v___x_889_;
}
}
else
{
size_t v___x_890_; size_t v___x_891_; lean_object* v___x_892_; 
v___x_890_ = lean_usize_of_nat(v___x_883_);
lean_dec(v___x_883_);
v___x_891_ = lean_usize_of_nat(v___x_884_);
v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_860_, v___x_861_, v_tail_868_, v___x_890_, v___x_891_, v_init_863_);
return v___x_892_;
}
}
}
}
else
{
lean_object* v_root_893_; lean_object* v_tail_894_; lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v_root_893_ = lean_ctor_get(v_t_862_, 0);
v_tail_894_ = lean_ctor_get(v_t_862_, 1);
lean_inc(v___x_861_);
lean_inc(v_f_860_);
v___x_895_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(v_f_860_, v___x_861_, v_root_893_, v_init_863_);
v___x_896_ = lean_array_get_size(v_tail_894_);
v___x_897_ = lean_nat_dec_lt(v___x_865_, v___x_896_);
if (v___x_897_ == 0)
{
lean_dec(v___x_861_);
lean_dec(v_f_860_);
return v___x_895_;
}
else
{
uint8_t v___x_898_; 
v___x_898_ = lean_nat_dec_le(v___x_896_, v___x_896_);
if (v___x_898_ == 0)
{
if (v___x_897_ == 0)
{
lean_dec(v___x_861_);
lean_dec(v_f_860_);
return v___x_895_;
}
else
{
size_t v___x_899_; size_t v___x_900_; lean_object* v___x_901_; 
v___x_899_ = ((size_t)0ULL);
v___x_900_ = lean_usize_of_nat(v___x_896_);
v___x_901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_860_, v___x_861_, v_tail_894_, v___x_899_, v___x_900_, v___x_895_);
return v___x_901_;
}
}
else
{
size_t v___x_902_; size_t v___x_903_; lean_object* v___x_904_; 
v___x_902_ = ((size_t)0ULL);
v___x_903_ = lean_usize_of_nat(v___x_896_);
v___x_904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_860_, v___x_861_, v_tail_894_, v___x_902_, v___x_903_, v___x_895_);
return v___x_904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(lean_object* v_f_905_, lean_object* v_ctx_x3f_906_, lean_object* v_a_907_, lean_object* v_x_908_){
_start:
{
switch(lean_obj_tag(v_x_908_))
{
case 0:
{
lean_object* v_i_909_; lean_object* v_t_910_; lean_object* v___x_911_; 
v_i_909_ = lean_ctor_get(v_x_908_, 0);
lean_inc_ref(v_i_909_);
v_t_910_ = lean_ctor_get(v_x_908_, 1);
lean_inc_ref(v_t_910_);
lean_dec_ref(v_x_908_);
v___x_911_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_909_, v_ctx_x3f_906_);
v_ctx_x3f_906_ = v___x_911_;
v_x_908_ = v_t_910_;
goto _start;
}
case 1:
{
lean_object* v_i_913_; lean_object* v_children_914_; lean_object* v___y_916_; 
v_i_913_ = lean_ctor_get(v_x_908_, 0);
lean_inc_ref(v_i_913_);
v_children_914_ = lean_ctor_get(v_x_908_, 1);
lean_inc_ref(v_children_914_);
if (lean_obj_tag(v_ctx_x3f_906_) == 0)
{
lean_dec_ref(v_x_908_);
v___y_916_ = v_a_907_;
goto v___jp_915_;
}
else
{
lean_object* v_val_920_; lean_object* v___x_921_; 
v_val_920_ = lean_ctor_get(v_ctx_x3f_906_, 0);
lean_inc(v_f_905_);
lean_inc(v_val_920_);
v___x_921_ = lean_apply_3(v_f_905_, v_val_920_, v_x_908_, v_a_907_);
v___y_916_ = v___x_921_;
goto v___jp_915_;
}
v___jp_915_:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_906_, v_i_913_);
lean_dec_ref(v_i_913_);
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(v_f_905_, v___x_917_, v_children_914_, v___y_916_, v___x_918_);
lean_dec_ref(v_children_914_);
return v___x_919_;
}
}
default: 
{
lean_dec_ref(v_x_908_);
lean_dec(v_ctx_x3f_906_);
lean_dec(v_f_905_);
return v_a_907_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(lean_object* v_f_922_, lean_object* v___x_923_, lean_object* v_as_924_, size_t v_i_925_, size_t v_stop_926_, lean_object* v_b_927_){
_start:
{
uint8_t v___x_928_; 
v___x_928_ = lean_usize_dec_eq(v_i_925_, v_stop_926_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; size_t v___x_931_; size_t v___x_932_; 
v___x_929_ = lean_array_uget_borrowed(v_as_924_, v_i_925_);
lean_inc(v___x_929_);
lean_inc(v___x_923_);
lean_inc(v_f_922_);
v___x_930_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(v_f_922_, v___x_923_, v_b_927_, v___x_929_);
v___x_931_ = ((size_t)1ULL);
v___x_932_ = lean_usize_add(v_i_925_, v___x_931_);
v_i_925_ = v___x_932_;
v_b_927_ = v___x_930_;
goto _start;
}
else
{
lean_dec(v___x_923_);
lean_dec(v_f_922_);
return v_b_927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg___boxed(lean_object* v_f_934_, lean_object* v___x_935_, lean_object* v_as_936_, lean_object* v_i_937_, lean_object* v_stop_938_, lean_object* v_b_939_){
_start:
{
size_t v_i_boxed_940_; size_t v_stop_boxed_941_; lean_object* v_res_942_; 
v_i_boxed_940_ = lean_unbox_usize(v_i_937_);
lean_dec(v_i_937_);
v_stop_boxed_941_ = lean_unbox_usize(v_stop_938_);
lean_dec(v_stop_938_);
v_res_942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_934_, v___x_935_, v_as_936_, v_i_boxed_940_, v_stop_boxed_941_, v_b_939_);
lean_dec_ref(v_as_936_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_943_, lean_object* v___x_944_, lean_object* v_as_945_, lean_object* v_i_946_, lean_object* v_stop_947_, lean_object* v_b_948_){
_start:
{
size_t v_i_boxed_949_; size_t v_stop_boxed_950_; lean_object* v_res_951_; 
v_i_boxed_949_ = lean_unbox_usize(v_i_946_);
lean_dec(v_i_946_);
v_stop_boxed_950_ = lean_unbox_usize(v_stop_947_);
lean_dec(v_stop_947_);
v_res_951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_943_, v___x_944_, v_as_945_, v_i_boxed_949_, v_stop_boxed_950_, v_b_948_);
lean_dec_ref(v_as_945_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg___boxed(lean_object* v_f_952_, lean_object* v___x_953_, lean_object* v_x_954_, lean_object* v_x_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(v_f_952_, v___x_953_, v_x_954_, v_x_955_);
lean_dec_ref(v_x_954_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg___boxed(lean_object* v_f_957_, lean_object* v___x_958_, lean_object* v_x_959_, lean_object* v_x_960_, lean_object* v_x_961_, lean_object* v_x_962_){
_start:
{
size_t v_x_1544__boxed_963_; size_t v_x_1545__boxed_964_; lean_object* v_res_965_; 
v_x_1544__boxed_963_ = lean_unbox_usize(v_x_960_);
lean_dec(v_x_960_);
v_x_1545__boxed_964_ = lean_unbox_usize(v_x_961_);
lean_dec(v_x_961_);
v_res_965_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(v_f_957_, v___x_958_, v_x_959_, v_x_1544__boxed_963_, v_x_1545__boxed_964_, v_x_962_);
lean_dec_ref(v_x_959_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg___boxed(lean_object* v_f_966_, lean_object* v___x_967_, lean_object* v_t_968_, lean_object* v_init_969_, lean_object* v_start_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(v_f_966_, v___x_967_, v_t_968_, v_init_969_, v_start_970_);
lean_dec(v_start_970_);
lean_dec_ref(v_t_968_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go(lean_object* v_00_u03b1_972_, lean_object* v_f_973_, lean_object* v_ctx_x3f_974_, lean_object* v_a_975_, lean_object* v_x_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(v_f_973_, v_ctx_x3f_974_, v_a_975_, v_x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0(lean_object* v_00_u03b1_978_, lean_object* v_f_979_, lean_object* v___x_980_, lean_object* v_t_981_, lean_object* v_init_982_, lean_object* v_start_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(v_f_979_, v___x_980_, v_t_981_, v_init_982_, v_start_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___boxed(lean_object* v_00_u03b1_985_, lean_object* v_f_986_, lean_object* v___x_987_, lean_object* v_t_988_, lean_object* v_init_989_, lean_object* v_start_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0(v_00_u03b1_985_, v_f_986_, v___x_987_, v_t_988_, v_init_989_, v_start_990_);
lean_dec(v_start_990_);
lean_dec_ref(v_t_988_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0(lean_object* v_00_u03b1_992_, lean_object* v_f_993_, lean_object* v___x_994_, lean_object* v_x_995_, size_t v_x_996_, size_t v_x_997_, lean_object* v_x_998_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(v_f_993_, v___x_994_, v_x_995_, v_x_996_, v_x_997_, v_x_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1000_, lean_object* v_f_1001_, lean_object* v___x_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_, lean_object* v_x_1006_){
_start:
{
size_t v_x_1763__boxed_1007_; size_t v_x_1764__boxed_1008_; lean_object* v_res_1009_; 
v_x_1763__boxed_1007_ = lean_unbox_usize(v_x_1004_);
lean_dec(v_x_1004_);
v_x_1764__boxed_1008_ = lean_unbox_usize(v_x_1005_);
lean_dec(v_x_1005_);
v_res_1009_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0(v_00_u03b1_1000_, v_f_1001_, v___x_1002_, v_x_1003_, v_x_1763__boxed_1007_, v_x_1764__boxed_1008_, v_x_1006_);
lean_dec_ref(v_x_1003_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1(lean_object* v_00_u03b1_1010_, lean_object* v_f_1011_, lean_object* v___x_1012_, lean_object* v_as_1013_, size_t v_i_1014_, size_t v_stop_1015_, lean_object* v_b_1016_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_1011_, v___x_1012_, v_as_1013_, v_i_1014_, v_stop_1015_, v_b_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1018_, lean_object* v_f_1019_, lean_object* v___x_1020_, lean_object* v_as_1021_, lean_object* v_i_1022_, lean_object* v_stop_1023_, lean_object* v_b_1024_){
_start:
{
size_t v_i_boxed_1025_; size_t v_stop_boxed_1026_; lean_object* v_res_1027_; 
v_i_boxed_1025_ = lean_unbox_usize(v_i_1022_);
lean_dec(v_i_1022_);
v_stop_boxed_1026_ = lean_unbox_usize(v_stop_1023_);
lean_dec(v_stop_1023_);
v_res_1027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1(v_00_u03b1_1018_, v_f_1019_, v___x_1020_, v_as_1021_, v_i_boxed_1025_, v_stop_boxed_1026_, v_b_1024_);
lean_dec_ref(v_as_1021_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2(lean_object* v_00_u03b1_1028_, lean_object* v_f_1029_, lean_object* v___x_1030_, lean_object* v_x_1031_, lean_object* v_x_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(v_f_1029_, v___x_1030_, v_x_1031_, v_x_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1034_, lean_object* v_f_1035_, lean_object* v___x_1036_, lean_object* v_x_1037_, lean_object* v_x_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2(v_00_u03b1_1034_, v_f_1035_, v___x_1036_, v_x_1037_, v_x_1038_);
lean_dec_ref(v_x_1037_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1040_, lean_object* v_f_1041_, lean_object* v___x_1042_, lean_object* v_as_1043_, size_t v_i_1044_, size_t v_stop_1045_, lean_object* v_b_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_1041_, v___x_1042_, v_as_1043_, v_i_1044_, v_stop_1045_, v_b_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1048_, lean_object* v_f_1049_, lean_object* v___x_1050_, lean_object* v_as_1051_, lean_object* v_i_1052_, lean_object* v_stop_1053_, lean_object* v_b_1054_){
_start:
{
size_t v_i_boxed_1055_; size_t v_stop_boxed_1056_; lean_object* v_res_1057_; 
v_i_boxed_1055_ = lean_unbox_usize(v_i_1052_);
lean_dec(v_i_1052_);
v_stop_boxed_1056_ = lean_unbox_usize(v_stop_1053_);
lean_dec(v_stop_1053_);
v_res_1057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1(v_00_u03b1_1048_, v_f_1049_, v___x_1050_, v_as_1051_, v_i_boxed_1055_, v_stop_boxed_1056_, v_b_1054_);
lean_dec_ref(v_as_1051_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoTree___redArg(lean_object* v_init_1058_, lean_object* v_f_1059_, lean_object* v_x_1060_){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_box(0);
v___x_1062_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(v_f_1059_, v___x_1061_, v_init_1058_, v_x_1060_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoTree(lean_object* v_00_u03b1_1063_, lean_object* v_init_1064_, lean_object* v_f_1065_, lean_object* v_x_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Elab_InfoTree_foldInfoTree___redArg(v_init_1064_, v_f_1065_, v_x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0(lean_object* v_toPure_1068_, lean_object* v_result_1069_, lean_object* v_____do__lift_1070_){
_start:
{
if (lean_obj_tag(v_____do__lift_1070_) == 0)
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_apply_2(v_toPure_1068_, lean_box(0), v_result_1069_);
return v___x_1071_;
}
else
{
lean_object* v_val_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_val_1072_ = lean_ctor_get(v_____do__lift_1070_, 0);
lean_inc(v_val_1072_);
v___x_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1073_, 0, v_val_1072_);
lean_ctor_set(v___x_1073_, 1, v_result_1069_);
v___x_1074_ = lean_apply_2(v_toPure_1068_, lean_box(0), v___x_1073_);
return v___x_1074_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0___boxed(lean_object* v_toPure_1075_, lean_object* v_result_1076_, lean_object* v_____do__lift_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0(v_toPure_1075_, v_result_1076_, v_____do__lift_1077_);
lean_dec(v_____do__lift_1077_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__1(lean_object* v_toPure_1079_, lean_object* v_f_1080_, lean_object* v_toBind_1081_, lean_object* v_ctx_1082_, lean_object* v_info_1083_, lean_object* v_result_1084_){
_start:
{
if (lean_obj_tag(v_info_1083_) == 1)
{
lean_object* v_i_1085_; lean_object* v___f_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v_i_1085_ = lean_ctor_get(v_info_1083_, 0);
lean_inc_ref(v_i_1085_);
lean_dec_ref(v_info_1083_);
v___f_1086_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1086_, 0, v_toPure_1079_);
lean_closure_set(v___f_1086_, 1, v_result_1084_);
v___x_1087_ = lean_apply_2(v_f_1080_, v_ctx_1082_, v_i_1085_);
v___x_1088_ = lean_apply_4(v_toBind_1081_, lean_box(0), lean_box(0), v___x_1087_, v___f_1086_);
return v___x_1088_;
}
else
{
lean_object* v___x_1089_; 
lean_dec_ref(v_info_1083_);
lean_dec_ref(v_ctx_1082_);
lean_dec(v_toBind_1081_);
lean_dec(v_f_1080_);
v___x_1089_ = lean_apply_2(v_toPure_1079_, lean_box(0), v_result_1084_);
return v___x_1089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___redArg(lean_object* v_inst_1090_, lean_object* v_t_1091_, lean_object* v_f_1092_){
_start:
{
lean_object* v_toApplicative_1093_; lean_object* v_toBind_1094_; lean_object* v_toPure_1095_; lean_object* v___f_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v_toApplicative_1093_ = lean_ctor_get(v_inst_1090_, 0);
v_toBind_1094_ = lean_ctor_get(v_inst_1090_, 1);
v_toPure_1095_ = lean_ctor_get(v_toApplicative_1093_, 1);
lean_inc(v_toBind_1094_);
lean_inc(v_toPure_1095_);
v___f_1096_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__1), 6, 3);
lean_closure_set(v___f_1096_, 0, v_toPure_1095_);
lean_closure_set(v___f_1096_, 1, v_f_1092_);
lean_closure_set(v___f_1096_, 2, v_toBind_1094_);
v___x_1097_ = lean_box(0);
v___x_1098_ = l_Lean_Elab_InfoTree_foldInfoM___redArg(v_inst_1090_, v___f_1096_, v___x_1097_, v_t_1091_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM(lean_object* v_m_1099_, lean_object* v_00_u03b1_1100_, lean_object* v_inst_1101_, lean_object* v_t_1102_, lean_object* v_f_1103_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Lean_Elab_InfoTree_collectTermInfoM___redArg(v_inst_1101_, v_t_1102_, v_f_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Info_isTerm(lean_object* v_x_1105_){
_start:
{
if (lean_obj_tag(v_x_1105_) == 1)
{
uint8_t v___x_1106_; 
v___x_1106_ = 1;
return v___x_1106_;
}
else
{
uint8_t v___x_1107_; 
v___x_1107_ = 0;
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_isTerm___boxed(lean_object* v_x_1108_){
_start:
{
uint8_t v_res_1109_; lean_object* v_r_1110_; 
v_res_1109_ = l_Lean_Elab_Info_isTerm(v_x_1108_);
lean_dec_ref(v_x_1108_);
v_r_1110_ = lean_box(v_res_1109_);
return v_r_1110_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Info_isCompletion(lean_object* v_x_1111_){
_start:
{
if (lean_obj_tag(v_x_1111_) == 8)
{
uint8_t v___x_1112_; 
v___x_1112_ = 1;
return v___x_1112_;
}
else
{
uint8_t v___x_1113_; 
v___x_1113_ = 0;
return v___x_1113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_isCompletion___boxed(lean_object* v_x_1114_){
_start:
{
uint8_t v_res_1115_; lean_object* v_r_1116_; 
v_res_1115_ = l_Lean_Elab_Info_isCompletion(v_x_1114_);
lean_dec_ref(v_x_1114_);
v_r_1116_ = lean_box(v_res_1115_);
return v_r_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_getCompletionInfos___lam__0(lean_object* v_ctx_1117_, lean_object* v_info_1118_, lean_object* v_result_1119_){
_start:
{
if (lean_obj_tag(v_info_1118_) == 8)
{
lean_object* v_i_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v_i_1120_ = lean_ctor_get(v_info_1118_, 0);
lean_inc_ref(v_i_1120_);
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v_ctx_1117_);
lean_ctor_set(v___x_1121_, 1, v_i_1120_);
v___x_1122_ = lean_array_push(v_result_1119_, v___x_1121_);
return v___x_1122_;
}
else
{
lean_dec_ref(v_ctx_1117_);
return v_result_1119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_getCompletionInfos___lam__0___boxed(lean_object* v_ctx_1123_, lean_object* v_info_1124_, lean_object* v_result_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_Elab_InfoTree_getCompletionInfos___lam__0(v_ctx_1123_, v_info_1124_, v_result_1125_);
lean_dec_ref(v_info_1124_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_getCompletionInfos(lean_object* v_infoTree_1130_){
_start:
{
lean_object* v___f_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___f_1131_ = ((lean_object*)(l_Lean_Elab_InfoTree_getCompletionInfos___closed__0));
v___x_1132_ = ((lean_object*)(l_Lean_Elab_InfoTree_getCompletionInfos___closed__1));
v___x_1133_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_1131_, v___x_1132_, v_infoTree_1130_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_stx(lean_object* v_x_1134_){
_start:
{
switch(lean_obj_tag(v_x_1134_))
{
case 0:
{
lean_object* v_i_1135_; lean_object* v_toElabInfo_1136_; lean_object* v_stx_1137_; 
v_i_1135_ = lean_ctor_get(v_x_1134_, 0);
v_toElabInfo_1136_ = lean_ctor_get(v_i_1135_, 0);
v_stx_1137_ = lean_ctor_get(v_toElabInfo_1136_, 1);
lean_inc(v_stx_1137_);
return v_stx_1137_;
}
case 1:
{
lean_object* v_i_1138_; lean_object* v_toElabInfo_1139_; lean_object* v_stx_1140_; 
v_i_1138_ = lean_ctor_get(v_x_1134_, 0);
v_toElabInfo_1139_ = lean_ctor_get(v_i_1138_, 0);
v_stx_1140_ = lean_ctor_get(v_toElabInfo_1139_, 1);
lean_inc(v_stx_1140_);
return v_stx_1140_;
}
case 2:
{
lean_object* v_i_1141_; lean_object* v_toElabInfo_1142_; lean_object* v_stx_1143_; 
v_i_1141_ = lean_ctor_get(v_x_1134_, 0);
v_toElabInfo_1142_ = lean_ctor_get(v_i_1141_, 0);
v_stx_1143_ = lean_ctor_get(v_toElabInfo_1142_, 1);
lean_inc(v_stx_1143_);
return v_stx_1143_;
}
case 5:
{
lean_object* v_i_1144_; lean_object* v_stx_1145_; 
v_i_1144_ = lean_ctor_get(v_x_1134_, 0);
v_stx_1145_ = lean_ctor_get(v_i_1144_, 0);
lean_inc(v_stx_1145_);
return v_stx_1145_;
}
case 6:
{
lean_object* v_i_1146_; lean_object* v_stx_1147_; 
v_i_1146_ = lean_ctor_get(v_x_1134_, 0);
v_stx_1147_ = lean_ctor_get(v_i_1146_, 0);
lean_inc(v_stx_1147_);
return v_stx_1147_;
}
case 7:
{
lean_object* v_i_1148_; lean_object* v_stx_1149_; 
v_i_1148_ = lean_ctor_get(v_x_1134_, 0);
v_stx_1149_ = lean_ctor_get(v_i_1148_, 4);
lean_inc(v_stx_1149_);
return v_stx_1149_;
}
case 8:
{
lean_object* v_i_1150_; lean_object* v___x_1151_; 
v_i_1150_ = lean_ctor_get(v_x_1134_, 0);
v___x_1151_ = l_Lean_Elab_CompletionInfo_stx(v_i_1150_);
return v___x_1151_;
}
case 10:
{
lean_object* v_i_1152_; lean_object* v_stx_1153_; 
v_i_1152_ = lean_ctor_get(v_x_1134_, 0);
v_stx_1153_ = lean_ctor_get(v_i_1152_, 0);
lean_inc(v_stx_1153_);
return v_stx_1153_;
}
case 11:
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_box(0);
return v___x_1154_;
}
case 12:
{
lean_object* v_i_1155_; 
v_i_1155_ = lean_ctor_get(v_x_1134_, 0);
lean_inc(v_i_1155_);
return v_i_1155_;
}
case 13:
{
lean_object* v_i_1156_; lean_object* v_toTermInfo_1157_; lean_object* v_toElabInfo_1158_; lean_object* v_stx_1159_; 
v_i_1156_ = lean_ctor_get(v_x_1134_, 0);
v_toTermInfo_1157_ = lean_ctor_get(v_i_1156_, 0);
v_toElabInfo_1158_ = lean_ctor_get(v_toTermInfo_1157_, 0);
v_stx_1159_ = lean_ctor_get(v_toElabInfo_1158_, 1);
lean_inc(v_stx_1159_);
return v_stx_1159_;
}
case 16:
{
lean_object* v_i_1160_; lean_object* v_toElabInfo_1161_; lean_object* v_stx_1162_; 
v_i_1160_ = lean_ctor_get(v_x_1134_, 0);
v_toElabInfo_1161_ = lean_ctor_get(v_i_1160_, 0);
v_stx_1162_ = lean_ctor_get(v_toElabInfo_1161_, 1);
lean_inc(v_stx_1162_);
return v_stx_1162_;
}
default: 
{
lean_object* v_i_1163_; lean_object* v_stx_1164_; 
v_i_1163_ = lean_ctor_get(v_x_1134_, 0);
v_stx_1164_ = lean_ctor_get(v_i_1163_, 1);
lean_inc(v_stx_1164_);
return v_stx_1164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_stx___boxed(lean_object* v_x_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_Elab_Info_stx(v_x_1165_);
lean_dec_ref(v_x_1165_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_lctx(lean_object* v_x_1167_){
_start:
{
switch(lean_obj_tag(v_x_1167_))
{
case 1:
{
lean_object* v_i_1168_; lean_object* v_lctx_1169_; 
v_i_1168_ = lean_ctor_get(v_x_1167_, 0);
v_lctx_1169_ = lean_ctor_get(v_i_1168_, 1);
lean_inc_ref(v_lctx_1169_);
return v_lctx_1169_;
}
case 7:
{
lean_object* v_i_1170_; lean_object* v_lctx_1171_; 
v_i_1170_ = lean_ctor_get(v_x_1167_, 0);
v_lctx_1171_ = lean_ctor_get(v_i_1170_, 2);
lean_inc_ref(v_lctx_1171_);
return v_lctx_1171_;
}
case 13:
{
lean_object* v_i_1172_; lean_object* v_toTermInfo_1173_; lean_object* v_lctx_1174_; 
v_i_1172_ = lean_ctor_get(v_x_1167_, 0);
v_toTermInfo_1173_ = lean_ctor_get(v_i_1172_, 0);
v_lctx_1174_ = lean_ctor_get(v_toTermInfo_1173_, 1);
lean_inc_ref(v_lctx_1174_);
return v_lctx_1174_;
}
case 4:
{
lean_object* v_i_1175_; lean_object* v_lctx_1176_; 
v_i_1175_ = lean_ctor_get(v_x_1167_, 0);
v_lctx_1176_ = lean_ctor_get(v_i_1175_, 0);
lean_inc_ref(v_lctx_1176_);
return v_lctx_1176_;
}
case 8:
{
lean_object* v_i_1177_; lean_object* v___x_1178_; 
v_i_1177_ = lean_ctor_get(v_x_1167_, 0);
v___x_1178_ = l_Lean_Elab_CompletionInfo_lctx(v_i_1177_);
return v___x_1178_;
}
default: 
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_LocalContext_empty;
return v___x_1179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_lctx___boxed(lean_object* v_x_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_Elab_Info_lctx(v_x_1180_);
lean_dec_ref(v_x_1180_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_pos_x3f(lean_object* v_i_1182_){
_start:
{
lean_object* v___x_1183_; uint8_t v___x_1184_; lean_object* v___x_1185_; 
v___x_1183_ = l_Lean_Elab_Info_stx(v_i_1182_);
v___x_1184_ = 1;
v___x_1185_ = l_Lean_Syntax_getPos_x3f(v___x_1183_, v___x_1184_);
lean_dec(v___x_1183_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_pos_x3f___boxed(lean_object* v_i_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_Elab_Info_pos_x3f(v_i_1186_);
lean_dec_ref(v_i_1186_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_tailPos_x3f(lean_object* v_i_1188_){
_start:
{
lean_object* v___x_1189_; uint8_t v___x_1190_; lean_object* v___x_1191_; 
v___x_1189_ = l_Lean_Elab_Info_stx(v_i_1188_);
v___x_1190_ = 1;
v___x_1191_ = l_Lean_Syntax_getTailPos_x3f(v___x_1189_, v___x_1190_);
lean_dec(v___x_1189_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_tailPos_x3f___boxed(lean_object* v_i_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_Elab_Info_tailPos_x3f(v_i_1192_);
lean_dec_ref(v_i_1192_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_range_x3f(lean_object* v_i_1194_){
_start:
{
lean_object* v___x_1195_; uint8_t v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = l_Lean_Elab_Info_stx(v_i_1194_);
v___x_1196_ = 1;
v___x_1197_ = l_Lean_Syntax_getRange_x3f(v___x_1195_, v___x_1196_);
lean_dec(v___x_1195_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_range_x3f___boxed(lean_object* v_i_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_Elab_Info_range_x3f(v_i_1198_);
lean_dec_ref(v_i_1198_);
return v_res_1199_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Info_contains(lean_object* v_i_1200_, lean_object* v_pos_1201_, uint8_t v_includeStop_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_Elab_Info_range_x3f(v_i_1200_);
if (lean_obj_tag(v___x_1203_) == 0)
{
uint8_t v___x_1204_; 
v___x_1204_ = 0;
return v___x_1204_;
}
else
{
lean_object* v_val_1205_; uint8_t v___x_1206_; 
v_val_1205_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_val_1205_);
lean_dec_ref(v___x_1203_);
v___x_1206_ = l_Lean_Syntax_Range_contains(v_val_1205_, v_pos_1201_, v_includeStop_1202_);
lean_dec(v_val_1205_);
return v___x_1206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_contains___boxed(lean_object* v_i_1207_, lean_object* v_pos_1208_, lean_object* v_includeStop_1209_){
_start:
{
uint8_t v_includeStop_boxed_1210_; uint8_t v_res_1211_; lean_object* v_r_1212_; 
v_includeStop_boxed_1210_ = lean_unbox(v_includeStop_1209_);
v_res_1211_ = l_Lean_Elab_Info_contains(v_i_1207_, v_pos_1208_, v_includeStop_boxed_1210_);
lean_dec(v_pos_1208_);
lean_dec_ref(v_i_1207_);
v_r_1212_ = lean_box(v_res_1211_);
return v_r_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_size_x3f(lean_object* v_i_1213_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lean_Elab_Info_pos_x3f(v_i_1213_);
if (lean_obj_tag(v___x_1214_) == 0)
{
return v___x_1214_;
}
else
{
lean_object* v_val_1215_; lean_object* v___x_1216_; 
v_val_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_val_1215_);
lean_dec_ref(v___x_1214_);
v___x_1216_ = l_Lean_Elab_Info_tailPos_x3f(v_i_1213_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_dec(v_val_1215_);
return v___x_1216_;
}
else
{
lean_object* v_val_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1225_; 
v_val_1217_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1219_ = v___x_1216_;
v_isShared_1220_ = v_isSharedCheck_1225_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_val_1217_);
lean_dec(v___x_1216_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1225_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1221_ = lean_nat_sub(v_val_1217_, v_val_1215_);
lean_dec(v_val_1215_);
lean_dec(v_val_1217_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1221_);
v___x_1223_ = v___x_1219_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_size_x3f___boxed(lean_object* v_i_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_Elab_Info_size_x3f(v_i_1226_);
lean_dec_ref(v_i_1226_);
return v_res_1227_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Info_isSmaller(lean_object* v_i_u2081_1228_, lean_object* v_i_u2082_1229_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_Elab_Info_size_x3f(v_i_u2081_1228_);
if (lean_obj_tag(v___x_1230_) == 1)
{
lean_object* v_val_1231_; lean_object* v___x_1232_; 
v_val_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_val_1231_);
lean_dec_ref(v___x_1230_);
v___x_1232_ = l_Lean_Elab_Info_size_x3f(v_i_u2082_1229_);
if (lean_obj_tag(v___x_1232_) == 0)
{
uint8_t v___x_1233_; 
lean_dec(v_val_1231_);
v___x_1233_ = 1;
return v___x_1233_;
}
else
{
lean_object* v_val_1234_; uint8_t v___x_1235_; 
v_val_1234_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_val_1234_);
lean_dec_ref(v___x_1232_);
v___x_1235_ = lean_nat_dec_lt(v_val_1231_, v_val_1234_);
lean_dec(v_val_1234_);
lean_dec(v_val_1231_);
return v___x_1235_;
}
}
else
{
uint8_t v___x_1236_; 
lean_dec(v___x_1230_);
v___x_1236_ = 0;
return v___x_1236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_isSmaller___boxed(lean_object* v_i_u2081_1237_, lean_object* v_i_u2082_1238_){
_start:
{
uint8_t v_res_1239_; lean_object* v_r_1240_; 
v_res_1239_ = l_Lean_Elab_Info_isSmaller(v_i_u2081_1237_, v_i_u2082_1238_);
lean_dec_ref(v_i_u2082_1238_);
lean_dec_ref(v_i_u2081_1237_);
v_r_1240_ = lean_box(v_res_1239_);
return v_r_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_occursInside_x3f(lean_object* v_i_1241_, lean_object* v_hoverPos_1242_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_Elab_Info_pos_x3f(v_i_1241_);
if (lean_obj_tag(v___x_1243_) == 0)
{
return v___x_1243_;
}
else
{
lean_object* v_val_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1259_; 
v_val_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1259_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_val_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1259_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
uint8_t v___y_1249_; lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_Elab_Info_tailPos_x3f(v_i_1241_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_del_object(v___x_1246_);
lean_dec(v_val_1244_);
return v___x_1255_;
}
else
{
lean_object* v_val_1256_; uint8_t v___x_1257_; 
v_val_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_val_1256_);
lean_dec_ref(v___x_1255_);
v___x_1257_ = lean_nat_dec_le(v_val_1244_, v_hoverPos_1242_);
if (v___x_1257_ == 0)
{
lean_dec(v_val_1256_);
v___y_1249_ = v___x_1257_;
goto v___jp_1248_;
}
else
{
uint8_t v___x_1258_; 
v___x_1258_ = lean_nat_dec_lt(v_hoverPos_1242_, v_val_1256_);
lean_dec(v_val_1256_);
v___y_1249_ = v___x_1258_;
goto v___jp_1248_;
}
}
v___jp_1248_:
{
if (v___y_1249_ == 0)
{
lean_object* v___x_1250_; 
lean_del_object(v___x_1246_);
lean_dec(v_val_1244_);
v___x_1250_ = lean_box(0);
return v___x_1250_;
}
else
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1251_ = lean_nat_sub(v_hoverPos_1242_, v_val_1244_);
lean_dec(v_val_1244_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1251_);
v___x_1253_ = v___x_1246_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_occursInside_x3f___boxed(lean_object* v_i_1260_, lean_object* v_hoverPos_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_Elab_Info_occursInside_x3f(v_i_1260_, v_hoverPos_1261_);
lean_dec(v_hoverPos_1261_);
lean_dec_ref(v_i_1260_);
return v_res_1262_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Info_occursInOrOnBoundary(lean_object* v_i_1263_, lean_object* v_hoverPos_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_Elab_Info_pos_x3f(v_i_1263_);
if (lean_obj_tag(v___x_1265_) == 1)
{
lean_object* v_val_1266_; lean_object* v___x_1267_; 
v_val_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_val_1266_);
lean_dec_ref(v___x_1265_);
v___x_1267_ = l_Lean_Elab_Info_tailPos_x3f(v_i_1263_);
if (lean_obj_tag(v___x_1267_) == 1)
{
lean_object* v_val_1268_; uint8_t v___x_1269_; 
v_val_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_val_1268_);
lean_dec_ref(v___x_1267_);
v___x_1269_ = lean_nat_dec_le(v_val_1266_, v_hoverPos_1264_);
lean_dec(v_val_1266_);
if (v___x_1269_ == 0)
{
lean_dec(v_val_1268_);
return v___x_1269_;
}
else
{
uint8_t v___x_1270_; 
v___x_1270_ = lean_nat_dec_le(v_hoverPos_1264_, v_val_1268_);
lean_dec(v_val_1268_);
return v___x_1270_;
}
}
else
{
uint8_t v___x_1271_; 
lean_dec(v___x_1267_);
lean_dec(v_val_1266_);
v___x_1271_ = 0;
return v___x_1271_;
}
}
else
{
uint8_t v___x_1272_; 
lean_dec(v___x_1265_);
v___x_1272_ = 0;
return v___x_1272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_occursInOrOnBoundary___boxed(lean_object* v_i_1273_, lean_object* v_hoverPos_1274_){
_start:
{
uint8_t v_res_1275_; lean_object* v_r_1276_; 
v_res_1275_ = l_Lean_Elab_Info_occursInOrOnBoundary(v_i_1273_, v_hoverPos_1274_);
lean_dec(v_hoverPos_1274_);
lean_dec_ref(v_i_1273_);
v_r_1276_ = lean_box(v_res_1275_);
return v_r_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0(lean_object* v_p_1277_, lean_object* v_ctx_1278_, lean_object* v_i_1279_, lean_object* v_x_1280_){
_start:
{
lean_object* v___x_1281_; uint8_t v___x_1282_; 
lean_inc_ref(v_i_1279_);
v___x_1281_ = lean_apply_1(v_p_1277_, v_i_1279_);
v___x_1282_ = lean_unbox(v___x_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; 
lean_dec_ref(v_i_1279_);
lean_dec_ref(v_ctx_1278_);
v___x_1283_ = lean_box(0);
return v___x_1283_;
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1284_, 0, v_ctx_1278_);
lean_ctor_set(v___x_1284_, 1, v_i_1279_);
v___x_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
return v___x_1285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0___boxed(lean_object* v_p_1286_, lean_object* v_ctx_1287_, lean_object* v_i_1288_, lean_object* v_x_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0(v_p_1286_, v_ctx_1287_, v_i_1288_, v_x_1289_);
lean_dec_ref(v_x_1289_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(lean_object* v_as_1291_, size_t v_i_1292_, size_t v_stop_1293_, lean_object* v_b_1294_){
_start:
{
lean_object* v___y_1296_; uint8_t v___x_1300_; 
v___x_1300_ = lean_usize_dec_eq(v_i_1292_, v_stop_1293_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; lean_object* v_fst_1302_; lean_object* v_fst_1303_; uint8_t v___x_1304_; 
v___x_1301_ = lean_array_uget_borrowed(v_as_1291_, v_i_1292_);
v_fst_1302_ = lean_ctor_get(v___x_1301_, 0);
v_fst_1303_ = lean_ctor_get(v_b_1294_, 0);
v___x_1304_ = lean_nat_dec_lt(v_fst_1302_, v_fst_1303_);
if (v___x_1304_ == 0)
{
v___y_1296_ = v_b_1294_;
goto v___jp_1295_;
}
else
{
v___y_1296_ = v___x_1301_;
goto v___jp_1295_;
}
}
else
{
lean_inc_ref(v_b_1294_);
return v_b_1294_;
}
v___jp_1295_:
{
size_t v___x_1297_; size_t v___x_1298_; 
v___x_1297_ = ((size_t)1ULL);
v___x_1298_ = lean_usize_add(v_i_1292_, v___x_1297_);
v_i_1292_ = v___x_1298_;
v_b_1294_ = v___y_1296_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1___boxed(lean_object* v_as_1305_, lean_object* v_i_1306_, lean_object* v_stop_1307_, lean_object* v_b_1308_){
_start:
{
size_t v_i_boxed_1309_; size_t v_stop_boxed_1310_; lean_object* v_res_1311_; 
v_i_boxed_1309_ = lean_unbox_usize(v_i_1306_);
lean_dec(v_i_1306_);
v_stop_boxed_1310_ = lean_unbox_usize(v_stop_1307_);
lean_dec(v_stop_1307_);
v_res_1311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(v_as_1305_, v_i_boxed_1309_, v_stop_boxed_1310_, v_b_1308_);
lean_dec_ref(v_b_1308_);
lean_dec_ref(v_as_1305_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1(lean_object* v_as_1312_){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1313_ = lean_unsigned_to_nat(0u);
v___x_1314_ = lean_array_get_size(v_as_1312_);
v___x_1315_ = lean_nat_dec_lt(v___x_1313_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; 
v___x_1316_ = lean_box(0);
return v___x_1316_;
}
else
{
lean_object* v_a0_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v_a0_1317_ = lean_array_fget_borrowed(v_as_1312_, v___x_1313_);
v___x_1318_ = lean_unsigned_to_nat(1u);
v___x_1319_ = lean_nat_dec_lt(v___x_1318_, v___x_1314_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; 
lean_inc(v_a0_1317_);
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v_a0_1317_);
return v___x_1320_;
}
else
{
uint8_t v___x_1321_; 
v___x_1321_ = lean_nat_dec_le(v___x_1314_, v___x_1314_);
if (v___x_1321_ == 0)
{
if (v___x_1319_ == 0)
{
lean_object* v___x_1322_; 
lean_inc(v_a0_1317_);
v___x_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1322_, 0, v_a0_1317_);
return v___x_1322_;
}
else
{
size_t v___x_1323_; size_t v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1323_ = ((size_t)1ULL);
v___x_1324_ = lean_usize_of_nat(v___x_1314_);
v___x_1325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(v_as_1312_, v___x_1323_, v___x_1324_, v_a0_1317_);
v___x_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
return v___x_1326_;
}
}
else
{
size_t v___x_1327_; size_t v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1327_ = ((size_t)1ULL);
v___x_1328_ = lean_usize_of_nat(v___x_1314_);
v___x_1329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(v_as_1312_, v___x_1327_, v___x_1328_, v_a0_1317_);
v___x_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
return v___x_1330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1___boxed(lean_object* v_as_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1(v_as_1331_);
lean_dec_ref(v_as_1331_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__0(lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
if (lean_obj_tag(v_a_1333_) == 0)
{
lean_object* v___x_1335_; 
v___x_1335_ = lean_array_to_list(v_a_1334_);
return v___x_1335_;
}
else
{
lean_object* v_head_1336_; lean_object* v_tail_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1354_; 
v_head_1336_ = lean_ctor_get(v_a_1333_, 0);
v_tail_1337_ = lean_ctor_get(v_a_1333_, 1);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_a_1333_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1339_ = v_a_1333_;
v_isShared_1340_ = v_isSharedCheck_1354_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_tail_1337_);
lean_inc(v_head_1336_);
lean_dec(v_a_1333_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1354_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v_snd_1341_; lean_object* v___x_1342_; 
v_snd_1341_ = lean_ctor_get(v_head_1336_, 1);
v___x_1342_ = l_Lean_Elab_Info_pos_x3f(v_snd_1341_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_del_object(v___x_1339_);
lean_dec(v_head_1336_);
v_a_1333_ = v_tail_1337_;
goto _start;
}
else
{
lean_object* v_val_1344_; lean_object* v___x_1345_; 
v_val_1344_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_val_1344_);
lean_dec_ref(v___x_1342_);
v___x_1345_ = l_Lean_Elab_Info_tailPos_x3f(v_snd_1341_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_dec(v_val_1344_);
lean_del_object(v___x_1339_);
lean_dec(v_head_1336_);
v_a_1333_ = v_tail_1337_;
goto _start;
}
else
{
lean_object* v_val_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v_val_1347_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_val_1347_);
lean_dec_ref(v___x_1345_);
v___x_1348_ = lean_nat_sub(v_val_1347_, v_val_1344_);
lean_dec(v_val_1344_);
lean_dec(v_val_1347_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set_tag(v___x_1339_, 0);
lean_ctor_set(v___x_1339_, 1, v_head_1336_);
lean_ctor_set(v___x_1339_, 0, v___x_1348_);
v___x_1350_ = v___x_1339_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_head_1336_);
v___x_1350_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1351_; 
v___x_1351_ = lean_array_push(v_a_1334_, v___x_1350_);
v_a_1333_ = v_tail_1337_;
v_a_1334_ = v___x_1351_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f(lean_object* v_p_1357_, lean_object* v_t_1358_){
_start:
{
lean_object* v___f_1359_; lean_object* v_ts_1360_; lean_object* v___x_1361_; lean_object* v_infos_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___f_1359_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1359_, 0, v_p_1357_);
v_ts_1360_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_1359_, v_t_1358_);
v___x_1361_ = ((lean_object*)(l_Lean_Elab_InfoTree_smallestInfo_x3f___closed__0));
v_infos_1362_ = l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__0(v_ts_1360_, v___x_1361_);
v___x_1363_ = lean_array_mk(v_infos_1362_);
v___x_1364_ = l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1(v___x_1363_);
lean_dec_ref(v___x_1363_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_box(0);
return v___x_1365_;
}
else
{
lean_object* v_val_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1374_; 
v_val_1366_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1368_ = v___x_1364_;
v_isShared_1369_ = v_isSharedCheck_1374_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_val_1366_);
lean_dec(v___x_1364_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1374_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v_snd_1370_; lean_object* v___x_1372_; 
v_snd_1370_ = lean_ctor_get(v_val_1366_, 1);
lean_inc(v_snd_1370_);
lean_dec(v_val_1366_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v_snd_1370_);
v___x_1372_ = v___x_1368_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_snd_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_instBEqHoverableInfoPrio_beq(lean_object* v_x_1375_, lean_object* v_x_1376_){
_start:
{
uint8_t v_isHoverPosOnStop_1377_; lean_object* v_size_1378_; uint8_t v_isVariableInfo_1379_; uint8_t v_isPartialTermInfo_1380_; uint8_t v_isHoverPosOnStop_1381_; lean_object* v_size_1382_; uint8_t v_isVariableInfo_1383_; uint8_t v_isPartialTermInfo_1384_; uint8_t v___y_1386_; 
v_isHoverPosOnStop_1377_ = lean_ctor_get_uint8(v_x_1375_, sizeof(void*)*1);
v_size_1378_ = lean_ctor_get(v_x_1375_, 0);
v_isVariableInfo_1379_ = lean_ctor_get_uint8(v_x_1375_, sizeof(void*)*1 + 1);
v_isPartialTermInfo_1380_ = lean_ctor_get_uint8(v_x_1375_, sizeof(void*)*1 + 2);
v_isHoverPosOnStop_1381_ = lean_ctor_get_uint8(v_x_1376_, sizeof(void*)*1);
v_size_1382_ = lean_ctor_get(v_x_1376_, 0);
v_isVariableInfo_1383_ = lean_ctor_get_uint8(v_x_1376_, sizeof(void*)*1 + 1);
v_isPartialTermInfo_1384_ = lean_ctor_get_uint8(v_x_1376_, sizeof(void*)*1 + 2);
if (v_isHoverPosOnStop_1377_ == 0)
{
if (v_isHoverPosOnStop_1381_ == 0)
{
goto v___jp_1387_;
}
else
{
return v_isHoverPosOnStop_1377_;
}
}
else
{
if (v_isHoverPosOnStop_1381_ == 0)
{
return v_isHoverPosOnStop_1381_;
}
else
{
goto v___jp_1387_;
}
}
v___jp_1385_:
{
if (v___y_1386_ == 0)
{
return v___y_1386_;
}
else
{
if (v_isPartialTermInfo_1380_ == 0)
{
if (v_isPartialTermInfo_1384_ == 0)
{
return v___y_1386_;
}
else
{
return v_isPartialTermInfo_1380_;
}
}
else
{
return v_isPartialTermInfo_1384_;
}
}
}
v___jp_1387_:
{
uint8_t v___x_1388_; 
v___x_1388_ = lean_nat_dec_eq(v_size_1378_, v_size_1382_);
if (v___x_1388_ == 0)
{
return v___x_1388_;
}
else
{
if (v_isVariableInfo_1379_ == 0)
{
if (v_isVariableInfo_1383_ == 0)
{
v___y_1386_ = v___x_1388_;
goto v___jp_1385_;
}
else
{
return v_isVariableInfo_1379_;
}
}
else
{
v___y_1386_ = v_isVariableInfo_1383_;
goto v___jp_1385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instBEqHoverableInfoPrio_beq___boxed(lean_object* v_x_1389_, lean_object* v_x_1390_){
_start:
{
uint8_t v_res_1391_; lean_object* v_r_1392_; 
v_res_1391_ = l_Lean_Elab_instBEqHoverableInfoPrio_beq(v_x_1389_, v_x_1390_);
lean_dec_ref(v_x_1390_);
lean_dec_ref(v_x_1389_);
v_r_1392_ = lean_box(v_res_1391_);
return v_r_1392_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(lean_object* v_i1_1395_, lean_object* v_i2_1396_){
_start:
{
uint8_t v_isHoverPosOnStop_1397_; lean_object* v_size_1398_; uint8_t v_isVariableInfo_1399_; uint8_t v_isPartialTermInfo_1400_; uint8_t v___y_1412_; uint8_t v___y_1424_; 
v_isHoverPosOnStop_1397_ = lean_ctor_get_uint8(v_i1_1395_, sizeof(void*)*1);
v_size_1398_ = lean_ctor_get(v_i1_1395_, 0);
v_isVariableInfo_1399_ = lean_ctor_get_uint8(v_i1_1395_, sizeof(void*)*1 + 1);
v_isPartialTermInfo_1400_ = lean_ctor_get_uint8(v_i1_1395_, sizeof(void*)*1 + 2);
if (v_isHoverPosOnStop_1397_ == 0)
{
v___y_1424_ = v_isHoverPosOnStop_1397_;
goto v___jp_1423_;
}
else
{
uint8_t v_isHoverPosOnStop_1425_; 
v_isHoverPosOnStop_1425_ = lean_ctor_get_uint8(v_i2_1396_, sizeof(void*)*1);
if (v_isHoverPosOnStop_1425_ == 0)
{
uint8_t v___x_1426_; 
v___x_1426_ = 0;
return v___x_1426_;
}
else
{
uint8_t v___x_1427_; 
v___x_1427_ = 0;
v___y_1424_ = v___x_1427_;
goto v___jp_1423_;
}
}
v___jp_1401_:
{
if (v_isPartialTermInfo_1400_ == 0)
{
uint8_t v_isPartialTermInfo_1402_; 
v_isPartialTermInfo_1402_ = lean_ctor_get_uint8(v_i2_1396_, sizeof(void*)*1 + 2);
if (v_isPartialTermInfo_1402_ == 0)
{
uint8_t v___x_1403_; 
v___x_1403_ = 1;
return v___x_1403_;
}
else
{
uint8_t v___x_1404_; 
v___x_1404_ = 2;
return v___x_1404_;
}
}
else
{
uint8_t v_isPartialTermInfo_1405_; 
v_isPartialTermInfo_1405_ = lean_ctor_get_uint8(v_i2_1396_, sizeof(void*)*1 + 2);
if (v_isPartialTermInfo_1405_ == 0)
{
uint8_t v___x_1406_; 
v___x_1406_ = 0;
return v___x_1406_;
}
else
{
uint8_t v___x_1407_; 
v___x_1407_ = 1;
return v___x_1407_;
}
}
}
v___jp_1408_:
{
uint8_t v_isVariableInfo_1409_; 
v_isVariableInfo_1409_ = lean_ctor_get_uint8(v_i2_1396_, sizeof(void*)*1 + 1);
if (v_isVariableInfo_1409_ == 0)
{
goto v___jp_1401_;
}
else
{
uint8_t v___x_1410_; 
v___x_1410_ = 2;
return v___x_1410_;
}
}
v___jp_1411_:
{
lean_object* v_size_1413_; uint8_t v_isVariableInfo_1414_; uint8_t v___x_1415_; 
v_size_1413_ = lean_ctor_get(v_i2_1396_, 0);
v_isVariableInfo_1414_ = lean_ctor_get_uint8(v_i2_1396_, sizeof(void*)*1 + 1);
v___x_1415_ = lean_nat_dec_lt(v_size_1413_, v_size_1398_);
if (v___x_1415_ == 0)
{
uint8_t v___x_1416_; 
v___x_1416_ = lean_nat_dec_lt(v_size_1398_, v_size_1413_);
if (v___x_1416_ == 0)
{
if (v_isVariableInfo_1399_ == 0)
{
goto v___jp_1408_;
}
else
{
if (v_isVariableInfo_1414_ == 0)
{
uint8_t v___x_1417_; 
v___x_1417_ = 0;
return v___x_1417_;
}
else
{
if (v___y_1412_ == 0)
{
goto v___jp_1401_;
}
else
{
goto v___jp_1408_;
}
}
}
}
else
{
uint8_t v___x_1418_; 
v___x_1418_ = 2;
return v___x_1418_;
}
}
else
{
uint8_t v___x_1419_; 
v___x_1419_ = 0;
return v___x_1419_;
}
}
v___jp_1420_:
{
uint8_t v_isHoverPosOnStop_1421_; 
v_isHoverPosOnStop_1421_ = lean_ctor_get_uint8(v_i2_1396_, sizeof(void*)*1);
if (v_isHoverPosOnStop_1421_ == 0)
{
v___y_1412_ = v_isHoverPosOnStop_1421_;
goto v___jp_1411_;
}
else
{
uint8_t v___x_1422_; 
v___x_1422_ = 2;
return v___x_1422_;
}
}
v___jp_1423_:
{
if (v_isHoverPosOnStop_1397_ == 0)
{
goto v___jp_1420_;
}
else
{
if (v___y_1424_ == 0)
{
v___y_1412_ = v___y_1424_;
goto v___jp_1411_;
}
else
{
goto v___jp_1420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instOrdHoverableInfoPrio___lam__0___boxed(lean_object* v_i1_1428_, lean_object* v_i2_1429_){
_start:
{
uint8_t v_res_1430_; lean_object* v_r_1431_; 
v_res_1430_ = l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(v_i1_1428_, v_i2_1429_);
lean_dec_ref(v_i2_1429_);
lean_dec_ref(v_i1_1428_);
v_r_1431_ = lean_box(v_res_1430_);
return v_r_1431_;
}
}
static lean_object* _init_l_Lean_Elab_instLEHoverableInfoPrio(void){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_box(0);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMaxHoverableInfoPrio___lam__0(lean_object* v_x_1435_, lean_object* v_y_1436_){
_start:
{
uint8_t v___x_1437_; 
v___x_1437_ = l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(v_x_1435_, v_y_1436_);
if (v___x_1437_ == 2)
{
lean_inc_ref(v_x_1435_);
return v_x_1435_;
}
else
{
lean_inc_ref(v_y_1436_);
return v_y_1436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMaxHoverableInfoPrio___lam__0___boxed(lean_object* v_x_1438_, lean_object* v_y_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_Elab_instMaxHoverableInfoPrio___lam__0(v_x_1438_, v_y_1439_);
lean_dec_ref(v_y_1439_);
lean_dec_ref(v_x_1438_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0(lean_object* v_x_1443_){
_start:
{
lean_object* v_fst_1444_; 
v_fst_1444_ = lean_ctor_get(v_x_1443_, 0);
lean_inc(v_fst_1444_);
return v_fst_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0___boxed(lean_object* v_x_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0(v_x_1445_);
lean_dec_ref(v_x_1445_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1(lean_object* v_r_x3f_1447_){
_start:
{
if (lean_obj_tag(v_r_x3f_1447_) == 0)
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_box(0);
return v___x_1448_;
}
else
{
lean_object* v_val_1449_; 
v_val_1449_ = lean_ctor_get(v_r_x3f_1447_, 0);
lean_inc(v_val_1449_);
return v_val_1449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1___boxed(lean_object* v_r_x3f_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1(v_r_x3f_1450_);
lean_dec(v_r_x3f_1450_);
return v_res_1451_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2(lean_object* v___x_1452_, lean_object* v_maxPrio_x3f_1453_, lean_object* v_x_1454_){
_start:
{
lean_object* v_fst_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v_fst_1455_ = lean_ctor_get(v_x_1454_, 0);
lean_inc(v_fst_1455_);
v___x_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1456_, 0, v_fst_1455_);
v___x_1457_ = l_Option_instBEq_beq___redArg(v___x_1452_, v___x_1456_, v_maxPrio_x3f_1453_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2___boxed(lean_object* v___x_1458_, lean_object* v_maxPrio_x3f_1459_, lean_object* v_x_1460_){
_start:
{
uint8_t v_res_1461_; lean_object* v_r_1462_; 
v_res_1461_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2(v___x_1458_, v_maxPrio_x3f_1459_, v_x_1460_);
lean_dec_ref(v_x_1460_);
v_r_1462_ = lean_box(v_res_1461_);
return v_r_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3(lean_object* v___f_1475_, lean_object* v___f_1476_, lean_object* v___x_1477_, lean_object* v_toPure_1478_, lean_object* v_ctx_1479_, lean_object* v_info_1480_, lean_object* v_children_1481_, lean_object* v_hoverPos_1482_, uint8_t v_includeStop_1483_, lean_object* v_results_1484_){
_start:
{
lean_object* v___y_1486_; uint8_t v___y_1487_; uint8_t v___y_1488_; uint8_t v___y_1489_; uint8_t v___y_1496_; lean_object* v___y_1497_; uint8_t v___y_1498_; uint8_t v___y_1499_; uint8_t v___y_1500_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v_maxPrio_x3f_1506_; lean_object* v___f_1507_; lean_object* v_bestResult_x3f_1508_; 
v___x_1504_ = lean_box(0);
lean_inc(v_results_1484_);
v___x_1505_ = l_List_mapTR_loop___redArg(v___f_1475_, v_results_1484_, v___x_1504_);
v_maxPrio_x3f_1506_ = l_List_max_x3f___redArg(v___f_1476_, v___x_1505_);
v___f_1507_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_1507_, 0, v___x_1477_);
lean_closure_set(v___f_1507_, 1, v_maxPrio_x3f_1506_);
v_bestResult_x3f_1508_ = l_List_find_x3f___redArg(v___f_1507_, v_results_1484_);
if (lean_obj_tag(v_bestResult_x3f_1508_) == 1)
{
lean_object* v___x_1509_; 
lean_dec_ref(v_children_1481_);
lean_dec_ref(v_info_1480_);
lean_dec_ref(v_ctx_1479_);
v___x_1509_ = lean_apply_2(v_toPure_1478_, lean_box(0), v_bestResult_x3f_1508_);
return v___x_1509_;
}
else
{
lean_object* v___x_1510_; uint8_t v___y_1512_; uint8_t v___y_1513_; uint8_t v___y_1514_; uint8_t v___y_1527_; lean_object* v___x_1532_; uint8_t v___x_1533_; 
lean_dec(v_bestResult_x3f_1508_);
v___x_1510_ = l_Lean_Elab_Info_stx(v_info_1480_);
v___x_1532_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__1));
lean_inc(v___x_1510_);
v___x_1533_ = l_Lean_Syntax_isOfKind(v___x_1510_, v___x_1532_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; 
lean_inc_ref(v_info_1480_);
v___x_1534_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_1480_);
if (lean_obj_tag(v___x_1534_) == 0)
{
v___y_1527_ = v___x_1533_;
goto v___jp_1526_;
}
else
{
lean_object* v_val_1535_; lean_object* v_elaborator_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v_val_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_val_1535_);
lean_dec_ref(v___x_1534_);
v_elaborator_1536_ = lean_ctor_get(v_val_1535_, 0);
lean_inc(v_elaborator_1536_);
lean_dec(v_val_1535_);
v___x_1537_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6));
v___x_1538_ = lean_name_eq(v_elaborator_1536_, v___x_1537_);
lean_dec(v_elaborator_1536_);
v___y_1527_ = v___x_1538_;
goto v___jp_1526_;
}
}
else
{
v___y_1527_ = v___x_1533_;
goto v___jp_1526_;
}
v___jp_1511_:
{
lean_object* v___x_1515_; 
v___x_1515_ = l_Lean_Syntax_getRange_x3f(v___x_1510_, v___y_1513_);
lean_dec(v___x_1510_);
if (lean_obj_tag(v___x_1515_) == 1)
{
lean_object* v_val_1516_; uint8_t v___x_1517_; 
v_val_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_val_1516_);
lean_dec_ref(v___x_1515_);
v___x_1517_ = l_Lean_Syntax_Range_contains(v_val_1516_, v_hoverPos_1482_, v_includeStop_1483_);
if (v___x_1517_ == 0)
{
lean_dec(v_val_1516_);
lean_dec_ref(v_children_1481_);
lean_dec_ref(v_info_1480_);
lean_dec_ref(v_ctx_1479_);
goto v___jp_1501_;
}
else
{
if (v___y_1514_ == 0)
{
lean_dec(v_val_1516_);
lean_dec_ref(v_children_1481_);
lean_dec_ref(v_info_1480_);
lean_dec_ref(v_ctx_1479_);
goto v___jp_1501_;
}
else
{
lean_object* v_start_1518_; lean_object* v_stop_1519_; uint8_t v___x_1520_; lean_object* v___x_1521_; 
v_start_1518_ = lean_ctor_get(v_val_1516_, 0);
lean_inc(v_start_1518_);
v_stop_1519_ = lean_ctor_get(v_val_1516_, 1);
lean_inc(v_stop_1519_);
lean_dec(v_val_1516_);
v___x_1520_ = lean_nat_dec_eq(v_stop_1519_, v_hoverPos_1482_);
v___x_1521_ = lean_nat_sub(v_stop_1519_, v_start_1518_);
lean_dec(v_start_1518_);
lean_dec(v_stop_1519_);
if (lean_obj_tag(v_info_1480_) == 1)
{
lean_object* v_i_1522_; lean_object* v_expr_1523_; 
v_i_1522_ = lean_ctor_get(v_info_1480_, 0);
v_expr_1523_ = lean_ctor_get(v_i_1522_, 3);
if (lean_obj_tag(v_expr_1523_) == 1)
{
v___y_1496_ = v___y_1512_;
v___y_1497_ = v___x_1521_;
v___y_1498_ = v___x_1520_;
v___y_1499_ = v___y_1513_;
v___y_1500_ = v___y_1513_;
goto v___jp_1495_;
}
else
{
v___y_1496_ = v___y_1512_;
v___y_1497_ = v___x_1521_;
v___y_1498_ = v___x_1520_;
v___y_1499_ = v___y_1513_;
v___y_1500_ = v___y_1512_;
goto v___jp_1495_;
}
}
else
{
v___y_1496_ = v___y_1512_;
v___y_1497_ = v___x_1521_;
v___y_1498_ = v___x_1520_;
v___y_1499_ = v___y_1513_;
v___y_1500_ = v___y_1512_;
goto v___jp_1495_;
}
}
}
}
else
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_dec(v___x_1515_);
lean_dec_ref(v_children_1481_);
lean_dec_ref(v_info_1480_);
lean_dec_ref(v_ctx_1479_);
v___x_1524_ = lean_box(0);
v___x_1525_ = lean_apply_2(v_toPure_1478_, lean_box(0), v___x_1524_);
return v___x_1525_;
}
}
v___jp_1526_:
{
if (v___y_1527_ == 0)
{
uint8_t v___x_1528_; 
v___x_1528_ = 1;
switch(lean_obj_tag(v_info_1480_))
{
case 7:
{
v___y_1512_ = v___y_1527_;
v___y_1513_ = v___x_1528_;
v___y_1514_ = v___x_1528_;
goto v___jp_1511_;
}
case 5:
{
v___y_1512_ = v___y_1527_;
v___y_1513_ = v___x_1528_;
v___y_1514_ = v___x_1528_;
goto v___jp_1511_;
}
case 6:
{
v___y_1512_ = v___y_1527_;
v___y_1513_ = v___x_1528_;
v___y_1514_ = v___x_1528_;
goto v___jp_1511_;
}
default: 
{
lean_object* v___x_1529_; 
lean_inc_ref(v_info_1480_);
v___x_1529_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_1480_);
if (lean_obj_tag(v___x_1529_) == 0)
{
v___y_1512_ = v___y_1527_;
v___y_1513_ = v___x_1528_;
v___y_1514_ = v___y_1527_;
goto v___jp_1511_;
}
else
{
lean_dec_ref(v___x_1529_);
v___y_1512_ = v___y_1527_;
v___y_1513_ = v___x_1528_;
v___y_1514_ = v___x_1528_;
goto v___jp_1511_;
}
}
}
}
else
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_dec(v___x_1510_);
lean_dec_ref(v_children_1481_);
lean_dec_ref(v_info_1480_);
lean_dec_ref(v_ctx_1479_);
v___x_1530_ = lean_box(0);
v___x_1531_ = lean_apply_2(v_toPure_1478_, lean_box(0), v___x_1530_);
return v___x_1531_;
}
}
}
v___jp_1485_:
{
lean_object* v_priority_1490_; lean_object* v_result_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v_priority_1490_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_priority_1490_, 0, v___y_1486_);
lean_ctor_set_uint8(v_priority_1490_, sizeof(void*)*1, v___y_1487_);
lean_ctor_set_uint8(v_priority_1490_, sizeof(void*)*1 + 1, v___y_1488_);
lean_ctor_set_uint8(v_priority_1490_, sizeof(void*)*1 + 2, v___y_1489_);
v_result_1491_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_result_1491_, 0, v_ctx_1479_);
lean_ctor_set(v_result_1491_, 1, v_info_1480_);
lean_ctor_set(v_result_1491_, 2, v_children_1481_);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v_priority_1490_);
lean_ctor_set(v___x_1492_, 1, v_result_1491_);
v___x_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
v___x_1494_ = lean_apply_2(v_toPure_1478_, lean_box(0), v___x_1493_);
return v___x_1494_;
}
v___jp_1495_:
{
if (lean_obj_tag(v_info_1480_) == 2)
{
v___y_1486_ = v___y_1497_;
v___y_1487_ = v___y_1498_;
v___y_1488_ = v___y_1500_;
v___y_1489_ = v___y_1499_;
goto v___jp_1485_;
}
else
{
v___y_1486_ = v___y_1497_;
v___y_1487_ = v___y_1498_;
v___y_1488_ = v___y_1500_;
v___y_1489_ = v___y_1496_;
goto v___jp_1485_;
}
}
v___jp_1501_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = lean_box(0);
v___x_1503_ = lean_apply_2(v_toPure_1478_, lean_box(0), v___x_1502_);
return v___x_1503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___boxed(lean_object* v___f_1539_, lean_object* v___f_1540_, lean_object* v___x_1541_, lean_object* v_toPure_1542_, lean_object* v_ctx_1543_, lean_object* v_info_1544_, lean_object* v_children_1545_, lean_object* v_hoverPos_1546_, lean_object* v_includeStop_1547_, lean_object* v_results_1548_){
_start:
{
uint8_t v_includeStop_boxed_1549_; lean_object* v_res_1550_; 
v_includeStop_boxed_1549_ = lean_unbox(v_includeStop_1547_);
v_res_1550_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3(v___f_1539_, v___f_1540_, v___x_1541_, v_toPure_1542_, v_ctx_1543_, v_info_1544_, v_children_1545_, v_hoverPos_1546_, v_includeStop_boxed_1549_, v_results_1548_);
lean_dec(v_hoverPos_1546_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4(lean_object* v___f_1553_, lean_object* v___f_1554_, lean_object* v___x_1555_, lean_object* v_toPure_1556_, lean_object* v_hoverPos_1557_, uint8_t v_includeStop_1558_, lean_object* v___f_1559_, lean_object* v_filter_1560_, lean_object* v_toBind_1561_, lean_object* v_ctx_1562_, lean_object* v_info_1563_, lean_object* v_children_1564_, lean_object* v_results_1565_){
_start:
{
lean_object* v___x_1566_; lean_object* v___f_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1566_ = lean_box(v_includeStop_1558_);
lean_inc_ref(v_children_1564_);
lean_inc_ref(v_info_1563_);
lean_inc_ref(v_ctx_1562_);
v___f_1567_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_1567_, 0, v___f_1553_);
lean_closure_set(v___f_1567_, 1, v___f_1554_);
lean_closure_set(v___f_1567_, 2, v___x_1555_);
lean_closure_set(v___f_1567_, 3, v_toPure_1556_);
lean_closure_set(v___f_1567_, 4, v_ctx_1562_);
lean_closure_set(v___f_1567_, 5, v_info_1563_);
lean_closure_set(v___f_1567_, 6, v_children_1564_);
lean_closure_set(v___f_1567_, 7, v_hoverPos_1557_);
lean_closure_set(v___f_1567_, 8, v___x_1566_);
v___x_1568_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___closed__0));
v___x_1569_ = l_List_filterMapTR_go___redArg(v___f_1559_, v_results_1565_, v___x_1568_);
v___x_1570_ = lean_apply_4(v_filter_1560_, v_ctx_1562_, v_info_1563_, v_children_1564_, v___x_1569_);
v___x_1571_ = lean_apply_4(v_toBind_1561_, lean_box(0), lean_box(0), v___x_1570_, v___f_1567_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___boxed(lean_object* v___f_1572_, lean_object* v___f_1573_, lean_object* v___x_1574_, lean_object* v_toPure_1575_, lean_object* v_hoverPos_1576_, lean_object* v_includeStop_1577_, lean_object* v___f_1578_, lean_object* v_filter_1579_, lean_object* v_toBind_1580_, lean_object* v_ctx_1581_, lean_object* v_info_1582_, lean_object* v_children_1583_, lean_object* v_results_1584_){
_start:
{
uint8_t v_includeStop_boxed_1585_; lean_object* v_res_1586_; 
v_includeStop_boxed_1585_ = lean_unbox(v_includeStop_1577_);
v_res_1586_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4(v___f_1572_, v___f_1573_, v___x_1574_, v_toPure_1575_, v_hoverPos_1576_, v_includeStop_boxed_1585_, v___f_1578_, v_filter_1579_, v_toBind_1580_, v_ctx_1581_, v_info_1582_, v_children_1583_, v_results_1584_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__6(lean_object* v_toPure_1587_, lean_object* v_results_1588_){
_start:
{
if (lean_obj_tag(v_results_1588_) == 0)
{
goto v___jp_1589_;
}
else
{
lean_object* v_val_1592_; 
v_val_1592_ = lean_ctor_get(v_results_1588_, 0);
lean_inc(v_val_1592_);
lean_dec_ref(v_results_1588_);
if (lean_obj_tag(v_val_1592_) == 0)
{
goto v___jp_1589_;
}
else
{
lean_object* v_val_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1609_; 
v_val_1593_ = lean_ctor_get(v_val_1592_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_val_1592_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1595_ = v_val_1592_;
v_isShared_1596_ = v_isSharedCheck_1609_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_val_1593_);
lean_dec(v_val_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1609_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v_snd_1597_; lean_object* v_info_1598_; lean_object* v___x_1600_; 
v_snd_1597_ = lean_ctor_get(v_val_1593_, 1);
lean_inc(v_snd_1597_);
lean_dec(v_val_1593_);
v_info_1598_ = lean_ctor_get(v_snd_1597_, 1);
lean_inc_ref(v_info_1598_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v_snd_1597_);
v___x_1600_ = v___x_1595_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_snd_1597_);
v___x_1600_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
if (lean_obj_tag(v_info_1598_) == 1)
{
lean_object* v_i_1601_; lean_object* v_expr_1602_; uint8_t v___x_1603_; 
v_i_1601_ = lean_ctor_get(v_info_1598_, 0);
lean_inc_ref(v_i_1601_);
lean_dec_ref(v_info_1598_);
v_expr_1602_ = lean_ctor_get(v_i_1601_, 3);
lean_inc_ref(v_expr_1602_);
lean_dec_ref(v_i_1601_);
v___x_1603_ = l_Lean_Expr_isSyntheticSorry(v_expr_1602_);
lean_dec_ref(v_expr_1602_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_apply_2(v_toPure_1587_, lean_box(0), v___x_1600_);
return v___x_1604_;
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
lean_dec_ref(v___x_1600_);
v___x_1605_ = lean_box(0);
v___x_1606_ = lean_apply_2(v_toPure_1587_, lean_box(0), v___x_1605_);
return v___x_1606_;
}
}
else
{
lean_object* v___x_1607_; 
lean_dec_ref(v_info_1598_);
v___x_1607_ = lean_apply_2(v_toPure_1587_, lean_box(0), v___x_1600_);
return v___x_1607_;
}
}
}
}
}
v___jp_1589_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_box(0);
v___x_1591_ = lean_apply_2(v_toPure_1587_, lean_box(0), v___x_1590_);
return v___x_1591_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg(lean_object* v_inst_1612_, lean_object* v_t_1613_, lean_object* v_hoverPos_1614_, uint8_t v_includeStop_1615_, lean_object* v_filter_1616_){
_start:
{
lean_object* v_toApplicative_1617_; lean_object* v_toBind_1618_; lean_object* v_toPure_1619_; lean_object* v___f_1620_; lean_object* v___f_1621_; lean_object* v___f_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v_postNode_1625_; lean_object* v___f_1626_; lean_object* v___f_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v_toApplicative_1617_ = lean_ctor_get(v_inst_1612_, 0);
v_toBind_1618_ = lean_ctor_get(v_inst_1612_, 1);
lean_inc_n(v_toBind_1618_, 2);
v_toPure_1619_ = lean_ctor_get(v_toApplicative_1617_, 1);
v___f_1620_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__0));
v___f_1621_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__1));
v___f_1622_ = ((lean_object*)(l_Lean_Elab_instMaxHoverableInfoPrio___closed__0));
v___x_1623_ = ((lean_object*)(l_Lean_Elab_instBEqHoverableInfoPrio___closed__0));
v___x_1624_ = lean_box(v_includeStop_1615_);
lean_inc_n(v_toPure_1619_, 3);
v_postNode_1625_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___boxed), 13, 9);
lean_closure_set(v_postNode_1625_, 0, v___f_1620_);
lean_closure_set(v_postNode_1625_, 1, v___f_1622_);
lean_closure_set(v_postNode_1625_, 2, v___x_1623_);
lean_closure_set(v_postNode_1625_, 3, v_toPure_1619_);
lean_closure_set(v_postNode_1625_, 4, v_hoverPos_1614_);
lean_closure_set(v_postNode_1625_, 5, v___x_1624_);
lean_closure_set(v_postNode_1625_, 6, v___f_1621_);
lean_closure_set(v_postNode_1625_, 7, v_filter_1616_);
lean_closure_set(v_postNode_1625_, 8, v_toBind_1618_);
v___f_1626_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__2___boxed), 4, 1);
lean_closure_set(v___f_1626_, 0, v_toPure_1619_);
v___f_1627_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__6), 2, 1);
lean_closure_set(v___f_1627_, 0, v_toPure_1619_);
v___x_1628_ = lean_box(0);
v___x_1629_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_1612_, v___f_1626_, v_postNode_1625_, v___x_1628_, v_t_1613_);
v___x_1630_ = lean_apply_4(v_toBind_1618_, lean_box(0), lean_box(0), v___x_1629_, v___f_1627_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___boxed(lean_object* v_inst_1631_, lean_object* v_t_1632_, lean_object* v_hoverPos_1633_, lean_object* v_includeStop_1634_, lean_object* v_filter_1635_){
_start:
{
uint8_t v_includeStop_boxed_1636_; lean_object* v_res_1637_; 
v_includeStop_boxed_1636_ = lean_unbox(v_includeStop_1634_);
v_res_1637_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg(v_inst_1631_, v_t_1632_, v_hoverPos_1633_, v_includeStop_boxed_1636_, v_filter_1635_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f(lean_object* v_m_1638_, lean_object* v_inst_1639_, lean_object* v_t_1640_, lean_object* v_hoverPos_1641_, uint8_t v_includeStop_1642_, lean_object* v_filter_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg(v_inst_1639_, v_t_1640_, v_hoverPos_1641_, v_includeStop_1642_, v_filter_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___boxed(lean_object* v_m_1645_, lean_object* v_inst_1646_, lean_object* v_t_1647_, lean_object* v_hoverPos_1648_, lean_object* v_includeStop_1649_, lean_object* v_filter_1650_){
_start:
{
uint8_t v_includeStop_boxed_1651_; lean_object* v_res_1652_; 
v_includeStop_boxed_1651_ = lean_unbox(v_includeStop_1649_);
v_res_1652_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f(v_m_1645_, v_inst_1646_, v_t_1647_, v_hoverPos_1648_, v_includeStop_boxed_1651_, v_filter_1650_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_type_x3f(lean_object* v_i_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
switch(lean_obj_tag(v_i_1653_))
{
case 1:
{
lean_object* v_i_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1684_; 
v_i_1659_ = lean_ctor_get(v_i_1653_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_i_1653_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1661_ = v_i_1653_;
v_isShared_1662_ = v_isSharedCheck_1684_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_i_1659_);
lean_dec(v_i_1653_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1684_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v_expr_1663_; lean_object* v___x_1664_; 
v_expr_1663_ = lean_ctor_get(v_i_1659_, 3);
lean_inc_ref(v_expr_1663_);
lean_dec_ref(v_i_1659_);
lean_inc(v_a_1657_);
lean_inc_ref(v_a_1656_);
lean_inc(v_a_1655_);
lean_inc_ref(v_a_1654_);
v___x_1664_ = lean_infer_type(v_expr_1663_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1675_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1667_ = v___x_1664_;
v_isShared_1668_ = v_isSharedCheck_1675_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1664_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1675_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 0, v_a_1665_);
v___x_1670_ = v___x_1661_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1672_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v___x_1670_);
v___x_1672_ = v___x_1667_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_del_object(v___x_1661_);
v_a_1676_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1664_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1664_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
}
case 7:
{
lean_object* v_i_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1710_; 
v_i_1685_ = lean_ctor_get(v_i_1653_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_i_1653_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1687_ = v_i_1653_;
v_isShared_1688_ = v_isSharedCheck_1710_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_i_1685_);
lean_dec(v_i_1653_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1710_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v_val_1689_; lean_object* v___x_1690_; 
v_val_1689_ = lean_ctor_get(v_i_1685_, 3);
lean_inc_ref(v_val_1689_);
lean_dec_ref(v_i_1685_);
lean_inc(v_a_1657_);
lean_inc_ref(v_a_1656_);
lean_inc(v_a_1655_);
lean_inc_ref(v_a_1654_);
v___x_1690_ = lean_infer_type(v_val_1689_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1701_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1701_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1701_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1688_ == 0)
{
lean_ctor_set_tag(v___x_1687_, 1);
lean_ctor_set(v___x_1687_, 0, v_a_1691_);
v___x_1696_ = v___x_1687_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1698_; 
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1696_);
v___x_1698_ = v___x_1693_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_del_object(v___x_1687_);
v_a_1702_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1690_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1690_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
case 13:
{
lean_object* v_i_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1737_; 
v_i_1711_ = lean_ctor_get(v_i_1653_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_i_1653_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1713_ = v_i_1653_;
v_isShared_1714_ = v_isSharedCheck_1737_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_i_1711_);
lean_dec(v_i_1653_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1737_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v_toTermInfo_1715_; lean_object* v_expr_1716_; lean_object* v___x_1717_; 
v_toTermInfo_1715_ = lean_ctor_get(v_i_1711_, 0);
lean_inc_ref(v_toTermInfo_1715_);
lean_dec_ref(v_i_1711_);
v_expr_1716_ = lean_ctor_get(v_toTermInfo_1715_, 3);
lean_inc_ref(v_expr_1716_);
lean_dec_ref(v_toTermInfo_1715_);
lean_inc(v_a_1657_);
lean_inc_ref(v_a_1656_);
lean_inc(v_a_1655_);
lean_inc_ref(v_a_1654_);
v___x_1717_ = lean_infer_type(v_expr_1716_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1728_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1720_ = v___x_1717_;
v_isShared_1721_ = v_isSharedCheck_1728_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1728_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1714_ == 0)
{
lean_ctor_set_tag(v___x_1713_, 1);
lean_ctor_set(v___x_1713_, 0, v_a_1718_);
v___x_1723_ = v___x_1713_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1725_; 
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1723_);
v___x_1725_ = v___x_1720_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1723_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_del_object(v___x_1713_);
v_a_1729_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1717_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1717_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
}
default: 
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec_ref(v_i_1653_);
v___x_1738_ = lean_box(0);
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
return v___x_1739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_type_x3f___boxed(lean_object* v_i_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_Elab_Info_type_x3f(v_i_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
lean_dec(v_a_1744_);
lean_dec_ref(v_a_1743_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(lean_object* v_name_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v___x_1750_; lean_object* v_env_1751_; lean_object* v___x_1752_; lean_object* v_toEnvExtension_1753_; lean_object* v_asyncMode_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1750_ = lean_st_ref_get(v___y_1748_);
v_env_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc_ref(v_env_1751_);
lean_dec(v___x_1750_);
v___x_1752_ = l_Lean_errorExplanationExt;
v_toEnvExtension_1753_ = lean_ctor_get(v___x_1752_, 0);
v_asyncMode_1754_ = lean_ctor_get(v_toEnvExtension_1753_, 2);
v___x_1755_ = lean_box(1);
v___x_1756_ = lean_box(0);
v___x_1757_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1755_, v___x_1752_, v_env_1751_, v_asyncMode_1754_, v___x_1756_);
v___x_1758_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1757_, v_name_1747_);
lean_dec(v___x_1757_);
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg___boxed(lean_object* v_name_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_name_1760_, v___y_1761_);
lean_dec(v___y_1761_);
lean_dec(v_name_1760_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0(lean_object* v_name_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_name_1764_, v___y_1768_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___boxed(lean_object* v_name_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0(v_name_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v_name_1771_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_docString_x3f(lean_object* v_i_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_){
_start:
{
lean_object* v___x_1784_; lean_object* v_env_1785_; lean_object* v___y_1787_; 
v___x_1784_ = lean_st_ref_get(v_a_1782_);
v_env_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc_ref(v_env_1785_);
lean_dec(v___x_1784_);
switch(lean_obj_tag(v_i_1778_))
{
case 13:
{
lean_object* v_i_1856_; lean_object* v_docString_x3f_1857_; 
v_i_1856_ = lean_ctor_get(v_i_1778_, 0);
v_docString_x3f_1857_ = lean_ctor_get(v_i_1856_, 2);
if (lean_obj_tag(v_docString_x3f_1857_) == 1)
{
lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_inc_ref(v_docString_x3f_1857_);
lean_dec_ref(v_env_1785_);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_i_1778_);
if (v_isSharedCheck_1864_ == 0)
{
lean_object* v_unused_1865_; 
v_unused_1865_ = lean_ctor_get(v_i_1778_, 0);
lean_dec(v_unused_1865_);
v___x_1859_ = v_i_1778_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_dec(v_i_1778_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
lean_ctor_set_tag(v___x_1859_, 0);
lean_ctor_set(v___x_1859_, 0, v_docString_x3f_1857_);
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_docString_x3f_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
else
{
lean_object* v_toTermInfo_1866_; lean_object* v_expr_1867_; lean_object* v___x_1868_; 
v_toTermInfo_1866_ = lean_ctor_get(v_i_1856_, 0);
v_expr_1867_ = lean_ctor_get(v_toTermInfo_1866_, 3);
v___x_1868_ = l_Lean_Expr_constName_x3f(v_expr_1867_);
if (lean_obj_tag(v___x_1868_) == 1)
{
lean_object* v_val_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1898_; 
lean_dec_ref(v_i_1778_);
v_val_1869_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1871_ = v___x_1868_;
v_isShared_1872_ = v_isSharedCheck_1898_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_val_1869_);
lean_dec(v___x_1868_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1898_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
uint8_t v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = 1;
v___x_1874_ = l_Lean_findDocString_x3f(v_env_1785_, v_val_1869_, v___x_1873_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_del_object(v___x_1871_);
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1874_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1874_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1897_; 
v_a_1883_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1885_ = v___x_1874_;
v_isShared_1886_ = v_isSharedCheck_1897_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1874_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1897_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v_ref_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v_ref_1887_ = lean_ctor_get(v_a_1781_, 5);
v___x_1888_ = lean_io_error_to_string(v_a_1883_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set_tag(v___x_1871_, 3);
lean_ctor_set(v___x_1871_, 0, v___x_1888_);
v___x_1890_ = v___x_1871_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1894_; 
v___x_1891_ = l_Lean_MessageData_ofFormat(v___x_1890_);
lean_inc(v_ref_1887_);
v___x_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1892_, 0, v_ref_1887_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1892_);
v___x_1894_ = v___x_1885_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1868_);
v___y_1787_ = v_a_1781_;
goto v___jp_1786_;
}
}
}
case 1:
{
lean_object* v_i_1899_; lean_object* v_expr_1900_; lean_object* v___x_1901_; 
v_i_1899_ = lean_ctor_get(v_i_1778_, 0);
v_expr_1900_ = lean_ctor_get(v_i_1899_, 3);
v___x_1901_ = l_Lean_Expr_constName_x3f(v_expr_1900_);
if (lean_obj_tag(v___x_1901_) == 1)
{
lean_object* v_val_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1931_; 
lean_dec_ref(v_i_1778_);
v_val_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1931_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_val_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1931_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
uint8_t v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = 1;
v___x_1907_ = l_Lean_findDocString_x3f(v_env_1785_, v_val_1902_, v___x_1906_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_del_object(v___x_1904_);
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1907_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1907_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1930_; 
v_a_1916_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1918_ = v___x_1907_;
v_isShared_1919_ = v_isSharedCheck_1930_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1907_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1930_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v_ref_1920_; lean_object* v___x_1921_; lean_object* v___x_1923_; 
v_ref_1920_ = lean_ctor_get(v_a_1781_, 5);
v___x_1921_ = lean_io_error_to_string(v_a_1916_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set_tag(v___x_1904_, 3);
lean_ctor_set(v___x_1904_, 0, v___x_1921_);
v___x_1923_ = v___x_1904_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1924_ = l_Lean_MessageData_ofFormat(v___x_1923_);
lean_inc(v_ref_1920_);
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v_ref_1920_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v___x_1925_);
v___x_1927_ = v___x_1918_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1901_);
v___y_1787_ = v_a_1781_;
goto v___jp_1786_;
}
}
case 7:
{
lean_object* v_i_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1962_; 
v_i_1932_ = lean_ctor_get(v_i_1778_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_i_1778_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1934_ = v_i_1778_;
v_isShared_1935_ = v_isSharedCheck_1962_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_i_1932_);
lean_dec(v_i_1778_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1962_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v_projName_1936_; uint8_t v___x_1937_; lean_object* v___x_1938_; 
v_projName_1936_ = lean_ctor_get(v_i_1932_, 0);
lean_inc(v_projName_1936_);
lean_dec_ref(v_i_1932_);
v___x_1937_ = 1;
v___x_1938_ = l_Lean_findDocString_x3f(v_env_1785_, v_projName_1936_, v___x_1937_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_del_object(v___x_1934_);
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1961_; 
v_a_1947_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1949_ = v___x_1938_;
v_isShared_1950_ = v_isSharedCheck_1961_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1938_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1961_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v_ref_1951_; lean_object* v___x_1952_; lean_object* v___x_1954_; 
v_ref_1951_ = lean_ctor_get(v_a_1781_, 5);
v___x_1952_ = lean_io_error_to_string(v_a_1947_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set_tag(v___x_1934_, 3);
lean_ctor_set(v___x_1934_, 0, v___x_1952_);
v___x_1954_ = v___x_1934_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1955_ = l_Lean_MessageData_ofFormat(v___x_1954_);
lean_inc(v_ref_1951_);
v___x_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1956_, 0, v_ref_1951_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v___x_1956_);
v___x_1958_ = v___x_1949_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1956_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
}
case 5:
{
lean_object* v_i_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_2032_; 
v_i_1963_ = lean_ctor_get(v_i_1778_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_i_1778_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_1965_ = v_i_1778_;
v_isShared_1966_ = v_isSharedCheck_2032_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_i_1963_);
lean_dec(v_i_1778_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_2032_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v_optionName_1967_; lean_object* v_declName_1968_; uint8_t v___x_1969_; lean_object* v___x_1970_; 
v_optionName_1967_ = lean_ctor_get(v_i_1963_, 1);
lean_inc(v_optionName_1967_);
v_declName_1968_ = lean_ctor_get(v_i_1963_, 2);
lean_inc(v_declName_1968_);
lean_dec_ref(v_i_1963_);
v___x_1969_ = 1;
v___x_1970_ = l_Lean_findDocString_x3f(v_env_1785_, v_declName_1968_, v___x_1969_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_2016_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1973_ = v___x_1970_;
v_isShared_1974_ = v_isSharedCheck_2016_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1970_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_2016_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
if (lean_obj_tag(v_a_1971_) == 1)
{
lean_object* v___x_1976_; 
lean_dec(v_optionName_1967_);
lean_del_object(v___x_1965_);
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
else
{
lean_object* v___x_1978_; 
lean_del_object(v___x_1973_);
lean_dec(v_a_1971_);
v___x_1978_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_2000_; 
lean_del_object(v___x_1965_);
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1981_ = v___x_1978_;
v_isShared_1982_ = v_isSharedCheck_2000_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1978_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_2000_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1979_, v_optionName_1967_);
lean_dec(v_optionName_1967_);
lean_dec(v_a_1979_);
if (lean_obj_tag(v___x_1983_) == 1)
{
lean_object* v_val_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1995_; 
v_val_1984_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1986_ = v___x_1983_;
v_isShared_1987_ = v_isSharedCheck_1995_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_val_1984_);
lean_dec(v___x_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1995_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1988_; lean_object* v___x_1990_; 
v___x_1988_ = l_Lean_OptionDecl_fullDescr(v_val_1984_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_1988_);
v___x_1990_ = v___x_1986_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1992_; 
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v___x_1990_);
v___x_1992_ = v___x_1981_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
else
{
lean_object* v___x_1996_; lean_object* v___x_1998_; 
lean_dec(v___x_1983_);
v___x_1996_ = lean_box(0);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v___x_1996_);
v___x_1998_ = v___x_1981_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2015_; 
lean_dec(v_optionName_1967_);
v_a_2001_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2003_ = v___x_1978_;
v_isShared_2004_ = v_isSharedCheck_2015_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1978_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2015_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v_ref_2005_; lean_object* v___x_2006_; lean_object* v___x_2008_; 
v_ref_2005_ = lean_ctor_get(v_a_1781_, 5);
v___x_2006_ = lean_io_error_to_string(v_a_2001_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set_tag(v___x_1965_, 3);
lean_ctor_set(v___x_1965_, 0, v___x_2006_);
v___x_2008_ = v___x_1965_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2012_; 
v___x_2009_ = l_Lean_MessageData_ofFormat(v___x_2008_);
lean_inc(v_ref_2005_);
v___x_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2010_, 0, v_ref_2005_);
lean_ctor_set(v___x_2010_, 1, v___x_2009_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2010_);
v___x_2012_ = v___x_2003_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2031_; 
lean_dec(v_optionName_1967_);
v_a_2017_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2019_ = v___x_1970_;
v_isShared_2020_ = v_isSharedCheck_2031_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_1970_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2031_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v_ref_2021_; lean_object* v___x_2022_; lean_object* v___x_2024_; 
v_ref_2021_ = lean_ctor_get(v_a_1781_, 5);
v___x_2022_ = lean_io_error_to_string(v_a_2017_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set_tag(v___x_1965_, 3);
lean_ctor_set(v___x_1965_, 0, v___x_2022_);
v___x_2024_ = v___x_1965_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
v___x_2025_ = l_Lean_MessageData_ofFormat(v___x_2024_);
lean_inc(v_ref_2021_);
v___x_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2026_, 0, v_ref_2021_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2026_);
v___x_2028_ = v___x_2019_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
}
}
case 6:
{
lean_object* v_i_2033_; lean_object* v_errorName_2034_; lean_object* v___x_2035_; lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2056_; 
lean_dec_ref(v_env_1785_);
v_i_2033_ = lean_ctor_get(v_i_1778_, 0);
lean_inc_ref(v_i_2033_);
lean_dec_ref(v_i_1778_);
v_errorName_2034_ = lean_ctor_get(v_i_2033_, 1);
lean_inc(v_errorName_2034_);
lean_dec_ref(v_i_2033_);
v___x_2035_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_errorName_2034_, v_a_1782_);
lean_dec(v_errorName_2034_);
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2038_ = v___x_2035_;
v_isShared_2039_ = v_isSharedCheck_2056_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2035_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2056_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
if (lean_obj_tag(v_a_2036_) == 1)
{
lean_object* v_val_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2051_; 
v_val_2040_ = lean_ctor_get(v_a_2036_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_a_2036_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2042_ = v_a_2036_;
v_isShared_2043_ = v_isSharedCheck_2051_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_val_2040_);
lean_dec(v_a_2036_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2051_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; lean_object* v___x_2046_; 
v___x_2044_ = l_Lean_ErrorExplanation_summaryWithSeverity(v_val_2040_);
lean_dec(v_val_2040_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2044_);
v___x_2046_ = v___x_2042_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v___x_2048_; 
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v___x_2046_);
v___x_2048_ = v___x_2038_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
else
{
lean_object* v___x_2052_; lean_object* v___x_2054_; 
lean_dec(v_a_2036_);
v___x_2052_ = lean_box(0);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v___x_2052_);
v___x_2054_ = v___x_2038_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
case 15:
{
lean_object* v_i_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2095_; 
v_i_2057_ = lean_ctor_get(v_i_1778_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_i_1778_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2059_ = v_i_1778_;
v_isShared_2060_ = v_isSharedCheck_2095_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_i_2057_);
lean_dec(v_i_1778_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2095_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_stx_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2093_; 
v_stx_2061_ = lean_ctor_get(v_i_2057_, 1);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_i_2057_);
if (v_isSharedCheck_2093_ == 0)
{
lean_object* v_unused_2094_; 
v_unused_2094_ = lean_ctor_get(v_i_2057_, 0);
lean_dec(v_unused_2094_);
v___x_2063_ = v_i_2057_;
v_isShared_2064_ = v_isSharedCheck_2093_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_stx_2061_);
lean_dec(v_i_2057_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2093_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2065_; uint8_t v___x_2066_; lean_object* v___x_2067_; 
v___x_2065_ = l_Lean_Syntax_getKind(v_stx_2061_);
v___x_2066_ = 1;
v___x_2067_ = l_Lean_findDocString_x3f(v_env_1785_, v___x_2065_, v___x_2066_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_del_object(v___x_2063_);
lean_del_object(v___x_2059_);
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2067_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2067_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2092_; 
v_a_2076_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2078_ = v___x_2067_;
v_isShared_2079_ = v_isSharedCheck_2092_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2067_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2092_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v_ref_2080_; lean_object* v___x_2081_; lean_object* v___x_2083_; 
v_ref_2080_ = lean_ctor_get(v_a_1781_, 5);
v___x_2081_ = lean_io_error_to_string(v_a_2076_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set_tag(v___x_2059_, 3);
lean_ctor_set(v___x_2059_, 0, v___x_2081_);
v___x_2083_ = v___x_2059_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2084_ = l_Lean_MessageData_ofFormat(v___x_2083_);
lean_inc(v_ref_2080_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 1, v___x_2084_);
lean_ctor_set(v___x_2063_, 0, v_ref_2080_);
v___x_2086_ = v___x_2063_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_ref_2080_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
lean_object* v___x_2088_; 
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2086_);
v___x_2088_ = v___x_2078_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
}
}
}
}
case 16:
{
lean_object* v_i_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2126_; 
v_i_2096_ = lean_ctor_get(v_i_1778_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v_i_1778_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2098_ = v_i_1778_;
v_isShared_2099_ = v_isSharedCheck_2126_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_i_2096_);
lean_dec(v_i_1778_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2126_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v_name_2100_; uint8_t v___x_2101_; lean_object* v___x_2102_; 
v_name_2100_ = lean_ctor_get(v_i_2096_, 1);
lean_inc(v_name_2100_);
lean_dec_ref(v_i_2096_);
v___x_2101_ = 1;
v___x_2102_ = l_Lean_findDocString_x3f(v_env_1785_, v_name_2100_, v___x_2101_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_del_object(v___x_2098_);
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2102_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2102_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2125_; 
v_a_2111_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2113_ = v___x_2102_;
v_isShared_2114_ = v_isSharedCheck_2125_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2102_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2125_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v_ref_2115_; lean_object* v___x_2116_; lean_object* v___x_2118_; 
v_ref_2115_ = lean_ctor_get(v_a_1781_, 5);
v___x_2116_ = lean_io_error_to_string(v_a_2111_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set_tag(v___x_2098_, 3);
lean_ctor_set(v___x_2098_, 0, v___x_2116_);
v___x_2118_ = v___x_2098_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2119_ = l_Lean_MessageData_ofFormat(v___x_2118_);
lean_inc(v_ref_2115_);
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v_ref_2115_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2120_);
v___x_2122_ = v___x_2113_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
}
default: 
{
v___y_1787_ = v_a_1781_;
goto v___jp_1786_;
}
}
v___jp_1786_:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_Elab_Info_toElabInfo_x3f(v_i_1778_);
if (lean_obj_tag(v___x_1788_) == 1)
{
lean_object* v_val_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1853_; 
v_val_1789_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1791_ = v___x_1788_;
v_isShared_1792_ = v_isSharedCheck_1853_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_val_1789_);
lean_dec(v___x_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1853_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v_elaborator_1793_; lean_object* v_stx_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1852_; 
v_elaborator_1793_ = lean_ctor_get(v_val_1789_, 0);
v_stx_1794_ = lean_ctor_get(v_val_1789_, 1);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_val_1789_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1796_ = v_val_1789_;
v_isShared_1797_ = v_isSharedCheck_1852_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_stx_1794_);
lean_inc(v_elaborator_1793_);
lean_dec(v_val_1789_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1852_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1798_; uint8_t v___x_1799_; lean_object* v___x_1800_; 
v___x_1798_ = l_Lean_Syntax_getKind(v_stx_1794_);
v___x_1799_ = 1;
lean_inc_ref(v_env_1785_);
v___x_1800_ = l_Lean_findDocString_x3f(v_env_1785_, v___x_1798_, v___x_1799_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1834_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1834_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1834_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
if (lean_obj_tag(v_a_1801_) == 0)
{
lean_object* v___x_1805_; 
lean_del_object(v___x_1803_);
v___x_1805_ = l_Lean_findDocString_x3f(v_env_1785_, v_elaborator_1793_, v___x_1799_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
lean_del_object(v___x_1796_);
lean_del_object(v___x_1791_);
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1805_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1805_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1830_; 
v_a_1814_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1816_ = v___x_1805_;
v_isShared_1817_ = v_isSharedCheck_1830_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1805_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1830_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v_ref_1818_; lean_object* v___x_1819_; lean_object* v___x_1821_; 
v_ref_1818_ = lean_ctor_get(v___y_1787_, 5);
v___x_1819_ = lean_io_error_to_string(v_a_1814_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set_tag(v___x_1791_, 3);
lean_ctor_set(v___x_1791_, 0, v___x_1819_);
v___x_1821_ = v___x_1791_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1822_ = l_Lean_MessageData_ofFormat(v___x_1821_);
lean_inc(v_ref_1818_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 1, v___x_1822_);
lean_ctor_set(v___x_1796_, 0, v_ref_1818_);
v___x_1824_ = v___x_1796_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_ref_1818_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1826_; 
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1824_);
v___x_1826_ = v___x_1816_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
}
else
{
lean_object* v___x_1832_; 
lean_del_object(v___x_1796_);
lean_dec(v_elaborator_1793_);
lean_del_object(v___x_1791_);
lean_dec_ref(v_env_1785_);
if (v_isShared_1804_ == 0)
{
v___x_1832_ = v___x_1803_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1801_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1851_; 
lean_dec(v_elaborator_1793_);
lean_dec_ref(v_env_1785_);
v_a_1835_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1837_ = v___x_1800_;
v_isShared_1838_ = v_isSharedCheck_1851_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1800_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1851_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v_ref_1839_; lean_object* v___x_1840_; lean_object* v___x_1842_; 
v_ref_1839_ = lean_ctor_get(v___y_1787_, 5);
v___x_1840_ = lean_io_error_to_string(v_a_1835_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set_tag(v___x_1791_, 3);
lean_ctor_set(v___x_1791_, 0, v___x_1840_);
v___x_1842_ = v___x_1791_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1843_; lean_object* v___x_1845_; 
v___x_1843_ = l_Lean_MessageData_ofFormat(v___x_1842_);
lean_inc(v_ref_1839_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 1, v___x_1843_);
lean_ctor_set(v___x_1796_, 0, v_ref_1839_);
v___x_1845_ = v___x_1796_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_ref_1839_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1847_; 
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1845_);
v___x_1847_ = v___x_1837_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
lean_dec(v___x_1788_);
lean_dec_ref(v_env_1785_);
v___x_1854_ = lean_box(0);
v___x_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
return v___x_1855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_docString_x3f___boxed(lean_object* v_i_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lean_Elab_Info_docString_x3f(v_i_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
lean_dec(v_a_2131_);
lean_dec_ref(v_a_2130_);
lean_dec(v_a_2129_);
lean_dec_ref(v_a_2128_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object* v_msgData_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v___x_2140_; lean_object* v_env_2141_; lean_object* v___x_2142_; lean_object* v_mctx_2143_; lean_object* v_lctx_2144_; lean_object* v_options_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2140_ = lean_st_ref_get(v___y_2138_);
v_env_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc_ref(v_env_2141_);
lean_dec(v___x_2140_);
v___x_2142_ = lean_st_ref_get(v___y_2136_);
v_mctx_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc_ref(v_mctx_2143_);
lean_dec(v___x_2142_);
v_lctx_2144_ = lean_ctor_get(v___y_2135_, 2);
v_options_2145_ = lean_ctor_get(v___y_2137_, 2);
lean_inc_ref(v_options_2145_);
lean_inc_ref(v_lctx_2144_);
v___x_2146_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2146_, 0, v_env_2141_);
lean_ctor_set(v___x_2146_, 1, v_mctx_2143_);
lean_ctor_set(v___x_2146_, 2, v_lctx_2144_);
lean_ctor_set(v___x_2146_, 3, v_options_2145_);
v___x_2147_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
lean_ctor_set(v___x_2147_, 1, v_msgData_2134_);
v___x_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v_ref_2162_; lean_object* v___x_2163_; lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2172_; 
v_ref_2162_ = lean_ctor_get(v___y_2159_, 5);
v___x_2163_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2172_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2172_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2168_; lean_object* v___x_2170_; 
lean_inc(v_ref_2162_);
v___x_2168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2168_, 0, v_ref_2162_);
lean_ctor_set(v___x_2168_, 1, v_a_2164_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set_tag(v___x_2166_, 1);
lean_ctor_set(v___x_2166_, 0, v___x_2168_);
v___x_2170_ = v___x_2166_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_2180_, lean_object* v_msg_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_fileName_2187_; lean_object* v_fileMap_2188_; lean_object* v_options_2189_; lean_object* v_currRecDepth_2190_; lean_object* v_maxRecDepth_2191_; lean_object* v_ref_2192_; lean_object* v_currNamespace_2193_; lean_object* v_openDecls_2194_; lean_object* v_initHeartbeats_2195_; lean_object* v_maxHeartbeats_2196_; lean_object* v_quotContext_2197_; lean_object* v_currMacroScope_2198_; uint8_t v_diag_2199_; lean_object* v_cancelTk_x3f_2200_; uint8_t v_suppressElabErrors_2201_; lean_object* v_inheritedTraceOptions_2202_; lean_object* v_ref_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v_fileName_2187_ = lean_ctor_get(v___y_2184_, 0);
v_fileMap_2188_ = lean_ctor_get(v___y_2184_, 1);
v_options_2189_ = lean_ctor_get(v___y_2184_, 2);
v_currRecDepth_2190_ = lean_ctor_get(v___y_2184_, 3);
v_maxRecDepth_2191_ = lean_ctor_get(v___y_2184_, 4);
v_ref_2192_ = lean_ctor_get(v___y_2184_, 5);
v_currNamespace_2193_ = lean_ctor_get(v___y_2184_, 6);
v_openDecls_2194_ = lean_ctor_get(v___y_2184_, 7);
v_initHeartbeats_2195_ = lean_ctor_get(v___y_2184_, 8);
v_maxHeartbeats_2196_ = lean_ctor_get(v___y_2184_, 9);
v_quotContext_2197_ = lean_ctor_get(v___y_2184_, 10);
v_currMacroScope_2198_ = lean_ctor_get(v___y_2184_, 11);
v_diag_2199_ = lean_ctor_get_uint8(v___y_2184_, sizeof(void*)*14);
v_cancelTk_x3f_2200_ = lean_ctor_get(v___y_2184_, 12);
v_suppressElabErrors_2201_ = lean_ctor_get_uint8(v___y_2184_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2202_ = lean_ctor_get(v___y_2184_, 13);
v_ref_2203_ = l_Lean_replaceRef(v_ref_2180_, v_ref_2192_);
lean_inc_ref(v_inheritedTraceOptions_2202_);
lean_inc(v_cancelTk_x3f_2200_);
lean_inc(v_currMacroScope_2198_);
lean_inc(v_quotContext_2197_);
lean_inc(v_maxHeartbeats_2196_);
lean_inc(v_initHeartbeats_2195_);
lean_inc(v_openDecls_2194_);
lean_inc(v_currNamespace_2193_);
lean_inc(v_maxRecDepth_2191_);
lean_inc(v_currRecDepth_2190_);
lean_inc_ref(v_options_2189_);
lean_inc_ref(v_fileMap_2188_);
lean_inc_ref(v_fileName_2187_);
v___x_2204_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2204_, 0, v_fileName_2187_);
lean_ctor_set(v___x_2204_, 1, v_fileMap_2188_);
lean_ctor_set(v___x_2204_, 2, v_options_2189_);
lean_ctor_set(v___x_2204_, 3, v_currRecDepth_2190_);
lean_ctor_set(v___x_2204_, 4, v_maxRecDepth_2191_);
lean_ctor_set(v___x_2204_, 5, v_ref_2203_);
lean_ctor_set(v___x_2204_, 6, v_currNamespace_2193_);
lean_ctor_set(v___x_2204_, 7, v_openDecls_2194_);
lean_ctor_set(v___x_2204_, 8, v_initHeartbeats_2195_);
lean_ctor_set(v___x_2204_, 9, v_maxHeartbeats_2196_);
lean_ctor_set(v___x_2204_, 10, v_quotContext_2197_);
lean_ctor_set(v___x_2204_, 11, v_currMacroScope_2198_);
lean_ctor_set(v___x_2204_, 12, v_cancelTk_x3f_2200_);
lean_ctor_set(v___x_2204_, 13, v_inheritedTraceOptions_2202_);
lean_ctor_set_uint8(v___x_2204_, sizeof(void*)*14, v_diag_2199_);
lean_ctor_set_uint8(v___x_2204_, sizeof(void*)*14 + 1, v_suppressElabErrors_2201_);
v___x_2205_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_2181_, v___y_2182_, v___y_2183_, v___x_2204_, v___y_2185_);
lean_dec_ref(v___x_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_2206_, lean_object* v_msg_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_2206_, v_msg_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v_ref_2206_);
return v_res_2213_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2214_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
return v___x_2216_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2217_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_2218_ = lean_unsigned_to_nat(0u);
v___x_2219_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
lean_ctor_set(v___x_2219_, 2, v___x_2218_);
lean_ctor_set(v___x_2219_, 3, v___x_2218_);
lean_ctor_set(v___x_2219_, 4, v___x_2217_);
lean_ctor_set(v___x_2219_, 5, v___x_2217_);
lean_ctor_set(v___x_2219_, 6, v___x_2217_);
lean_ctor_set(v___x_2219_, 7, v___x_2217_);
lean_ctor_set(v___x_2219_, 8, v___x_2217_);
lean_ctor_set(v___x_2219_, 9, v___x_2217_);
return v___x_2219_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2220_ = lean_unsigned_to_nat(32u);
v___x_2221_ = lean_mk_empty_array_with_capacity(v___x_2220_);
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
return v___x_2222_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2223_ = ((size_t)5ULL);
v___x_2224_ = lean_unsigned_to_nat(0u);
v___x_2225_ = lean_unsigned_to_nat(32u);
v___x_2226_ = lean_mk_empty_array_with_capacity(v___x_2225_);
v___x_2227_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_2228_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
lean_ctor_set(v___x_2228_, 1, v___x_2226_);
lean_ctor_set(v___x_2228_, 2, v___x_2224_);
lean_ctor_set(v___x_2228_, 3, v___x_2224_);
lean_ctor_set_usize(v___x_2228_, 4, v___x_2223_);
return v___x_2228_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2229_ = lean_box(1);
v___x_2230_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_2231_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_2232_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v___x_2230_);
lean_ctor_set(v___x_2232_, 2, v___x_2229_);
return v___x_2232_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_2235_ = l_Lean_stringToMessageData(v___x_2234_);
return v___x_2235_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_2238_ = l_Lean_stringToMessageData(v___x_2237_);
return v___x_2238_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_2241_ = l_Lean_stringToMessageData(v___x_2240_);
return v___x_2241_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_2244_ = l_Lean_stringToMessageData(v___x_2243_);
return v___x_2244_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2246_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_2247_ = l_Lean_stringToMessageData(v___x_2246_);
return v___x_2247_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_2250_ = l_Lean_stringToMessageData(v___x_2249_);
return v___x_2250_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_2253_ = l_Lean_stringToMessageData(v___x_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_2254_, lean_object* v_declHint_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v___x_2258_; lean_object* v_env_2259_; uint8_t v___x_2260_; 
v___x_2258_ = lean_st_ref_get(v___y_2256_);
v_env_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc_ref(v_env_2259_);
lean_dec(v___x_2258_);
v___x_2260_ = l_Lean_Name_isAnonymous(v_declHint_2255_);
if (v___x_2260_ == 0)
{
uint8_t v_isExporting_2261_; 
v_isExporting_2261_ = lean_ctor_get_uint8(v_env_2259_, sizeof(void*)*8);
if (v_isExporting_2261_ == 0)
{
lean_object* v___x_2262_; 
lean_dec_ref(v_env_2259_);
lean_dec(v_declHint_2255_);
v___x_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2262_, 0, v_msg_2254_);
return v___x_2262_;
}
else
{
lean_object* v___x_2263_; uint8_t v___x_2264_; 
lean_inc_ref(v_env_2259_);
v___x_2263_ = l_Lean_Environment_setExporting(v_env_2259_, v___x_2260_);
lean_inc(v_declHint_2255_);
lean_inc_ref(v___x_2263_);
v___x_2264_ = l_Lean_Environment_contains(v___x_2263_, v_declHint_2255_, v_isExporting_2261_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2265_; 
lean_dec_ref(v___x_2263_);
lean_dec_ref(v_env_2259_);
lean_dec(v_declHint_2255_);
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v_msg_2254_);
return v___x_2265_;
}
else
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v_c_2271_; lean_object* v___x_2272_; 
v___x_2266_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_2267_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_2268_ = l_Lean_Options_empty;
v___x_2269_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2263_);
lean_ctor_set(v___x_2269_, 1, v___x_2266_);
lean_ctor_set(v___x_2269_, 2, v___x_2267_);
lean_ctor_set(v___x_2269_, 3, v___x_2268_);
lean_inc(v_declHint_2255_);
v___x_2270_ = l_Lean_MessageData_ofConstName(v_declHint_2255_, v___x_2260_);
v_c_2271_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2271_, 0, v___x_2269_);
lean_ctor_set(v_c_2271_, 1, v___x_2270_);
v___x_2272_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2259_, v_declHint_2255_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_dec_ref(v_env_2259_);
lean_dec(v_declHint_2255_);
v___x_2273_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
lean_ctor_set(v___x_2274_, 1, v_c_2271_);
v___x_2275_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_2276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2274_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
v___x_2277_ = l_Lean_MessageData_note(v___x_2276_);
v___x_2278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2278_, 0, v_msg_2254_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
return v___x_2279_;
}
else
{
lean_object* v_val_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2315_; 
v_val_2280_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2282_ = v___x_2272_;
v_isShared_2283_ = v_isSharedCheck_2315_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_val_2280_);
lean_dec(v___x_2272_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2315_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v_mod_2287_; uint8_t v___x_2288_; 
v___x_2284_ = lean_box(0);
v___x_2285_ = l_Lean_Environment_header(v_env_2259_);
lean_dec_ref(v_env_2259_);
v___x_2286_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2285_);
v_mod_2287_ = lean_array_get(v___x_2284_, v___x_2286_, v_val_2280_);
lean_dec(v_val_2280_);
lean_dec_ref(v___x_2286_);
v___x_2288_ = l_Lean_isPrivateName(v_declHint_2255_);
lean_dec(v_declHint_2255_);
if (v___x_2288_ == 0)
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2300_; 
v___x_2289_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_2290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
lean_ctor_set(v___x_2290_, 1, v_c_2271_);
v___x_2291_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_2292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2290_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
v___x_2293_ = l_Lean_MessageData_ofName(v_mod_2287_);
v___x_2294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2292_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
v___x_2295_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_2296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2294_);
lean_ctor_set(v___x_2296_, 1, v___x_2295_);
v___x_2297_ = l_Lean_MessageData_note(v___x_2296_);
v___x_2298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2298_, 0, v_msg_2254_);
lean_ctor_set(v___x_2298_, 1, v___x_2297_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set_tag(v___x_2282_, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2298_);
v___x_2300_ = v___x_2282_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2298_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
else
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2302_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
lean_ctor_set(v___x_2303_, 1, v_c_2271_);
v___x_2304_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_2305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2303_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = l_Lean_MessageData_ofName(v_mod_2287_);
v___x_2307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2305_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_2309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2307_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
v___x_2310_ = l_Lean_MessageData_note(v___x_2309_);
v___x_2311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2311_, 0, v_msg_2254_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set_tag(v___x_2282_, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2311_);
v___x_2313_ = v___x_2282_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2316_; 
lean_dec_ref(v_env_2259_);
lean_dec(v_declHint_2255_);
v___x_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2316_, 0, v_msg_2254_);
return v___x_2316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_2317_, lean_object* v_declHint_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_2317_, v_declHint_2318_, v___y_2319_);
lean_dec(v___y_2319_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_2322_, lean_object* v_declHint_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v___x_2329_; lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2339_; 
v___x_2329_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_2322_, v_declHint_2323_, v___y_2327_);
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2339_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2339_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2337_; 
v___x_2334_ = l_Lean_unknownIdentifierMessageTag;
v___x_2335_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
lean_ctor_set(v___x_2335_, 1, v_a_2330_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2335_);
v___x_2337_ = v___x_2332_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_2340_, lean_object* v_declHint_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2340_, v_declHint_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_2348_, lean_object* v_msg_2349_, lean_object* v_declHint_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v___x_2356_; lean_object* v_a_2357_; lean_object* v___x_2358_; 
v___x_2356_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2349_, v_declHint_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_a_2357_);
lean_dec_ref(v___x_2356_);
v___x_2358_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_2348_, v_a_2357_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_2359_, lean_object* v_msg_2360_, lean_object* v_declHint_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_2359_, v_msg_2360_, v_declHint_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v_ref_2359_);
return v_res_2367_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_2370_ = l_Lean_stringToMessageData(v___x_2369_);
return v___x_2370_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2));
v___x_2373_ = l_Lean_stringToMessageData(v___x_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_2374_, lean_object* v_constName_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v___x_2381_; uint8_t v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2381_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_2382_ = 0;
lean_inc(v_constName_2375_);
v___x_2383_ = l_Lean_MessageData_ofConstName(v_constName_2375_, v___x_2382_);
v___x_2384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2381_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
v___x_2385_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_2386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2384_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
v___x_2387_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_2374_, v___x_2386_, v_constName_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_2388_, lean_object* v_constName_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2388_, v_constName_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v_ref_2388_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_ref_2402_; lean_object* v___x_2403_; 
v_ref_2402_ = lean_ctor_get(v___y_2399_, 5);
v___x_2403_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2402_, v_constName_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(lean_object* v_constName_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v___x_2417_; lean_object* v_env_2418_; uint8_t v___x_2419_; lean_object* v___x_2420_; 
v___x_2417_ = lean_st_ref_get(v___y_2415_);
v_env_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc_ref(v_env_2418_);
lean_dec(v___x_2417_);
v___x_2419_ = 0;
lean_inc(v_constName_2411_);
v___x_2420_ = l_Lean_Environment_find_x3f(v_env_2418_, v_constName_2411_, v___x_2419_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v___x_2421_; 
v___x_2421_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
return v___x_2421_;
}
else
{
lean_object* v_val_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
lean_dec(v_constName_2411_);
v_val_2422_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2420_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_val_2422_);
lean_dec(v___x_2420_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
lean_ctor_set_tag(v___x_2424_, 0);
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_val_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0___boxed(lean_object* v_constName_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(v_constName_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(lean_object* v_declName_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v___x_2443_; 
lean_inc(v_declName_2437_);
v___x_2443_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(v_declName_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2470_; 
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2470_ == 0)
{
lean_object* v_unused_2471_; 
v_unused_2471_ = lean_ctor_get(v___x_2443_, 0);
lean_dec(v_unused_2471_);
v___x_2445_ = v___x_2443_;
v_isShared_2446_ = v_isSharedCheck_2470_;
goto v_resetjp_2444_;
}
else
{
lean_dec(v___x_2443_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2470_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2447_; lean_object* v_env_2448_; lean_object* v___x_2449_; 
v___x_2447_ = lean_st_ref_get(v___y_2441_);
v_env_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc_ref(v_env_2448_);
lean_dec(v___x_2447_);
v___x_2449_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2448_, v_declName_2437_);
lean_dec(v_declName_2437_);
lean_dec_ref(v_env_2448_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v___x_2450_; lean_object* v___x_2452_; 
v___x_2450_ = lean_box(0);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2450_);
v___x_2452_ = v___x_2445_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2450_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
else
{
lean_object* v_val_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2469_; 
v_val_2454_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2456_ = v___x_2449_;
v_isShared_2457_ = v_isSharedCheck_2469_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_val_2454_);
lean_dec(v___x_2449_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2469_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2458_; lean_object* v_env_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2464_; 
v___x_2458_ = lean_st_ref_get(v___y_2441_);
v_env_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc_ref(v_env_2459_);
lean_dec(v___x_2458_);
v___x_2460_ = lean_box(0);
v___x_2461_ = l_Lean_Environment_allImportedModuleNames(v_env_2459_);
lean_dec_ref(v_env_2459_);
v___x_2462_ = lean_array_get(v___x_2460_, v___x_2461_, v_val_2454_);
lean_dec(v_val_2454_);
lean_dec_ref(v___x_2461_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 0, v___x_2462_);
v___x_2464_ = v___x_2456_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
lean_object* v___x_2466_; 
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2464_);
v___x_2466_ = v___x_2445_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
}
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
lean_dec(v_declName_2437_);
v_a_2472_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2443_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2443_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0___boxed(lean_object* v_declName_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(v_declName_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(lean_object* v_decl_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(v_decl_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2526_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2502_ = v___x_2499_;
v_isShared_2503_ = v_isSharedCheck_2526_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2499_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2526_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
if (lean_obj_tag(v_a_2500_) == 1)
{
lean_object* v_val_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2521_; 
v_val_2504_ = lean_ctor_get(v_a_2500_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_a_2500_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2506_ = v_a_2500_;
v_isShared_2507_ = v_isSharedCheck_2521_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_val_2504_);
lean_dec(v_a_2500_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2521_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; uint8_t v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2516_; 
v___x_2508_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__1));
v___x_2509_ = 1;
v___x_2510_ = l_Lean_Name_toString(v_val_2504_, v___x_2509_);
v___x_2511_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
v___x_2512_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2508_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
v___x_2513_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__3));
v___x_2514_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2512_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v___x_2514_);
v___x_2516_ = v___x_2506_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2518_; 
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 0, v___x_2516_);
v___x_2518_ = v___x_2502_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
else
{
lean_object* v___x_2522_; lean_object* v___x_2524_; 
lean_dec(v_a_2500_);
v___x_2522_ = lean_box(0);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 0, v___x_2522_);
v___x_2524_ = v___x_2502_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2522_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
v_a_2527_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2499_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2499_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___boxed(lean_object* v_decl_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(v_decl_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
lean_dec(v_a_2537_);
lean_dec_ref(v_a_2536_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2542_, lean_object* v_constName_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2550_, lean_object* v_constName_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1(v_00_u03b1_2550_, v_constName_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2558_, lean_object* v_ref_2559_, lean_object* v_constName_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2559_, v_constName_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2567_, lean_object* v_ref_2568_, lean_object* v_constName_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2567_, v_ref_2568_, v_constName_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v_ref_2568_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_2576_, lean_object* v_ref_2577_, lean_object* v_msg_2578_, lean_object* v_declHint_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v___x_2585_; 
v___x_2585_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_2577_, v_msg_2578_, v_declHint_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2586_, lean_object* v_ref_2587_, lean_object* v_msg_2588_, lean_object* v_declHint_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_00_u03b1_2586_, v_ref_2587_, v_msg_2588_, v_declHint_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v_ref_2587_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_2596_, lean_object* v_declHint_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_2596_, v_declHint_2597_, v___y_2601_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2604_, lean_object* v_declHint_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_2604_, v_declHint_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_2612_, lean_object* v_ref_2613_, lean_object* v_msg_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_2613_, v_msg_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2621_, lean_object* v_ref_2622_, lean_object* v_msg_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_2621_, v_ref_2622_, v_msg_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v_ref_2622_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_2630_, lean_object* v_msg_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2638_, lean_object* v_msg_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_2638_, v_msg_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
return v_res_2645_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(lean_object* v_a_2646_){
_start:
{
switch(lean_obj_tag(v_a_2646_))
{
case 3:
{
uint8_t v___x_2647_; 
v___x_2647_ = 1;
return v___x_2647_;
}
case 6:
{
lean_object* v_a_2648_; 
v_a_2648_ = lean_ctor_get(v_a_2646_, 0);
v_a_2646_ = v_a_2648_;
goto _start;
}
case 4:
{
lean_object* v_f_2650_; 
v_f_2650_ = lean_ctor_get(v_a_2646_, 1);
v_a_2646_ = v_f_2650_;
goto _start;
}
case 7:
{
lean_object* v_a_2652_; 
v_a_2652_ = lean_ctor_get(v_a_2646_, 1);
v_a_2646_ = v_a_2652_;
goto _start;
}
default: 
{
uint8_t v___x_2654_; 
v___x_2654_ = 0;
return v___x_2654_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat___boxed(lean_object* v_a_2655_){
_start:
{
uint8_t v_res_2656_; lean_object* v_r_2657_; 
v_res_2656_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(v_a_2655_);
lean_dec(v_a_2655_);
v_r_2657_ = lean_box(v_res_2656_);
return v_r_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(lean_object* v_e_2658_, lean_object* v___y_2659_){
_start:
{
uint8_t v___x_2661_; 
v___x_2661_ = l_Lean_Expr_hasMVar(v_e_2658_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; 
v___x_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2662_, 0, v_e_2658_);
return v___x_2662_;
}
else
{
lean_object* v___x_2663_; lean_object* v_mctx_2664_; lean_object* v___x_2665_; lean_object* v_fst_2666_; lean_object* v_snd_2667_; lean_object* v___x_2668_; lean_object* v_cache_2669_; lean_object* v_zetaDeltaFVarIds_2670_; lean_object* v_postponed_2671_; lean_object* v_diag_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2681_; 
v___x_2663_ = lean_st_ref_get(v___y_2659_);
v_mctx_2664_ = lean_ctor_get(v___x_2663_, 0);
lean_inc_ref(v_mctx_2664_);
lean_dec(v___x_2663_);
v___x_2665_ = l_Lean_instantiateMVarsCore(v_mctx_2664_, v_e_2658_);
v_fst_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_fst_2666_);
v_snd_2667_ = lean_ctor_get(v___x_2665_, 1);
lean_inc(v_snd_2667_);
lean_dec_ref(v___x_2665_);
v___x_2668_ = lean_st_ref_take(v___y_2659_);
v_cache_2669_ = lean_ctor_get(v___x_2668_, 1);
v_zetaDeltaFVarIds_2670_ = lean_ctor_get(v___x_2668_, 2);
v_postponed_2671_ = lean_ctor_get(v___x_2668_, 3);
v_diag_2672_ = lean_ctor_get(v___x_2668_, 4);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2681_ == 0)
{
lean_object* v_unused_2682_; 
v_unused_2682_ = lean_ctor_get(v___x_2668_, 0);
lean_dec(v_unused_2682_);
v___x_2674_ = v___x_2668_;
v_isShared_2675_ = v_isSharedCheck_2681_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_diag_2672_);
lean_inc(v_postponed_2671_);
lean_inc(v_zetaDeltaFVarIds_2670_);
lean_inc(v_cache_2669_);
lean_dec(v___x_2668_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2681_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v_snd_2667_);
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_snd_2667_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v_cache_2669_);
lean_ctor_set(v_reuseFailAlloc_2680_, 2, v_zetaDeltaFVarIds_2670_);
lean_ctor_set(v_reuseFailAlloc_2680_, 3, v_postponed_2671_);
lean_ctor_set(v_reuseFailAlloc_2680_, 4, v_diag_2672_);
v___x_2677_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2678_ = lean_st_ref_set(v___y_2659_, v___x_2677_);
v___x_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2679_, 0, v_fst_2666_);
return v___x_2679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg___boxed(lean_object* v_e_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_e_2683_, v___y_2684_);
lean_dec(v___y_2684_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0(lean_object* v_e_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v___x_2693_; 
v___x_2693_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_e_2687_, v___y_2689_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___boxed(lean_object* v_e_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0(v_e_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(lean_object* v_i_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_){
_start:
{
switch(lean_obj_tag(v_i_2712_))
{
case 1:
{
lean_object* v_i_2718_; lean_object* v_expr_2719_; uint8_t v_isDisplayableTerm_2720_; lean_object* v___x_2721_; lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2844_; 
v_i_2718_ = lean_ctor_get(v_i_2712_, 0);
lean_inc_ref(v_i_2718_);
lean_dec_ref(v_i_2712_);
v_expr_2719_ = lean_ctor_get(v_i_2718_, 3);
lean_inc_ref(v_expr_2719_);
v_isDisplayableTerm_2720_ = lean_ctor_get_uint8(v_i_2718_, sizeof(void*)*4 + 1);
lean_dec_ref(v_i_2718_);
v___x_2721_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_expr_2719_, v_a_2714_);
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2724_ = v___x_2721_;
v_isShared_2725_ = v_isSharedCheck_2844_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2721_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2844_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
uint8_t v___x_2726_; 
v___x_2726_ = l_Lean_Expr_isSort(v_a_2722_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; 
lean_del_object(v___x_2724_);
lean_inc(v_a_2716_);
lean_inc_ref(v_a_2715_);
lean_inc(v_a_2714_);
lean_inc_ref(v_a_2713_);
lean_inc(v_a_2722_);
v___x_2727_ = lean_infer_type(v_a_2722_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2728_; lean_object* v___x_2729_; lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2831_; 
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_a_2728_);
lean_dec_ref(v___x_2727_);
v___x_2729_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_a_2728_, v_a_2714_);
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2732_ = v___x_2729_;
v_isShared_2733_ = v_isSharedCheck_2831_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2729_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2831_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2734_; 
v___x_2734_ = l_Lean_Meta_ppExpr(v_a_2730_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_);
if (lean_obj_tag(v___x_2734_) == 0)
{
if (lean_obj_tag(v_a_2722_) == 4)
{
lean_object* v_declName_2735_; lean_object* v___x_2736_; 
lean_dec_ref(v___x_2734_);
v_declName_2735_ = lean_ctor_get(v_a_2722_, 0);
lean_inc_n(v_declName_2735_, 2);
lean_dec_ref(v_a_2722_);
v___x_2736_ = l_Lean_PrettyPrinter_ppSignature(v_declName_2735_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2738_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref(v___x_2736_);
v___x_2738_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(v_declName_2735_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2763_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2741_ = v___x_2738_;
v_isShared_2742_ = v_isSharedCheck_2763_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2738_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2763_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v_fmt_2743_; lean_object* v_infos_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2762_; 
v_fmt_2743_ = lean_ctor_get(v_a_2737_, 0);
v_infos_2744_ = lean_ctor_get(v_a_2737_, 1);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_a_2737_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2746_ = v_a_2737_;
v_isShared_2747_ = v_isSharedCheck_2762_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_infos_2744_);
lean_inc(v_fmt_2743_);
lean_dec(v_a_2737_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2762_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2753_; 
v___x_2748_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1));
v___x_2749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2748_);
lean_ctor_set(v___x_2749_, 1, v_fmt_2743_);
v___x_2750_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3));
v___x_2751_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2749_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 0, v___x_2751_);
v___x_2753_ = v___x_2746_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2751_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_infos_2744_);
v___x_2753_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
lean_object* v___x_2755_; 
if (v_isShared_2733_ == 0)
{
lean_ctor_set_tag(v___x_2732_, 1);
lean_ctor_set(v___x_2732_, 0, v___x_2753_);
v___x_2755_ = v___x_2732_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2753_);
v___x_2755_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
lean_object* v___x_2756_; lean_object* v___x_2758_; 
v___x_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
lean_ctor_set(v___x_2756_, 1, v_a_2739_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v___x_2756_);
v___x_2758_ = v___x_2741_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2756_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
lean_dec(v_a_2737_);
lean_del_object(v___x_2732_);
v_a_2764_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2738_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2738_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec(v_declName_2735_);
lean_del_object(v___x_2732_);
v_a_2772_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2736_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2736_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2781_; 
v_a_2780_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2780_);
lean_dec_ref(v___x_2734_);
lean_inc(v_a_2722_);
v___x_2781_ = l_Lean_Meta_ppExpr(v_a_2722_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2814_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2784_ = v___x_2781_;
v_isShared_2785_ = v_isSharedCheck_2814_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2781_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2814_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___y_2787_; uint8_t v___y_2807_; 
if (v_isDisplayableTerm_2720_ == 0)
{
if (lean_obj_tag(v_a_2722_) == 1)
{
lean_object* v_lctx_2808_; lean_object* v___x_2809_; 
v_lctx_2808_ = lean_ctor_get(v_a_2713_, 2);
lean_inc_ref(v_lctx_2808_);
v___x_2809_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_2808_, v_a_2722_);
lean_dec_ref(v_a_2722_);
if (lean_obj_tag(v___x_2809_) == 1)
{
lean_object* v_val_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; 
v_val_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_val_2810_);
lean_dec_ref(v___x_2809_);
v___x_2811_ = l_Lean_LocalDecl_userName(v_val_2810_);
lean_dec(v_val_2810_);
v___x_2812_ = l_Lean_Name_hasMacroScopes(v___x_2811_);
lean_dec(v___x_2811_);
if (v___x_2812_ == 0)
{
goto v___jp_2802_;
}
else
{
v___y_2807_ = v___x_2726_;
goto v___jp_2806_;
}
}
else
{
lean_dec(v___x_2809_);
v___y_2807_ = v___x_2726_;
goto v___jp_2806_;
}
}
else
{
uint8_t v___x_2813_; 
lean_dec(v_a_2722_);
v___x_2813_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(v_a_2782_);
v___y_2807_ = v___x_2813_;
goto v___jp_2806_;
}
}
else
{
lean_dec(v_a_2722_);
goto v___jp_2802_;
}
v___jp_2786_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2795_; 
v___x_2788_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1));
v___x_2789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
lean_ctor_set(v___x_2789_, 1, v___y_2787_);
v___x_2790_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3));
v___x_2791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2789_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
v___x_2792_ = lean_box(1);
v___x_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
if (v_isShared_2733_ == 0)
{
lean_ctor_set_tag(v___x_2732_, 1);
lean_ctor_set(v___x_2732_, 0, v___x_2793_);
v___x_2795_ = v___x_2732_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2793_);
v___x_2795_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2799_; 
v___x_2796_ = lean_box(0);
v___x_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2795_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v___x_2797_);
v___x_2799_ = v___x_2784_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2797_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
v___jp_2802_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2803_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5));
v___x_2804_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2804_, 0, v_a_2782_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
lean_ctor_set(v___x_2805_, 1, v_a_2780_);
v___y_2787_ = v___x_2805_;
goto v___jp_2786_;
}
v___jp_2806_:
{
if (v___y_2807_ == 0)
{
lean_dec(v_a_2782_);
v___y_2787_ = v_a_2780_;
goto v___jp_2786_;
}
else
{
goto v___jp_2802_;
}
}
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_dec(v_a_2780_);
lean_del_object(v___x_2732_);
lean_dec(v_a_2722_);
v_a_2815_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2781_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2781_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_del_object(v___x_2732_);
lean_dec(v_a_2722_);
v_a_2823_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2734_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2734_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_dec(v_a_2722_);
v_a_2832_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2727_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2727_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
else
{
lean_object* v___x_2840_; lean_object* v___x_2842_; 
lean_dec(v_a_2722_);
v___x_2840_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6));
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 0, v___x_2840_);
v___x_2842_ = v___x_2724_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2840_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
}
case 7:
{
lean_object* v_i_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2895_; 
v_i_2845_ = lean_ctor_get(v_i_2712_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v_i_2712_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2847_ = v_i_2712_;
v_isShared_2848_ = v_isSharedCheck_2895_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_i_2845_);
lean_dec(v_i_2712_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2895_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v_fieldName_2849_; lean_object* v_val_2850_; lean_object* v___x_2851_; 
v_fieldName_2849_ = lean_ctor_get(v_i_2845_, 1);
lean_inc(v_fieldName_2849_);
v_val_2850_ = lean_ctor_get(v_i_2845_, 3);
lean_inc_ref(v_val_2850_);
lean_dec_ref(v_i_2845_);
lean_inc(v_a_2716_);
lean_inc_ref(v_a_2715_);
lean_inc(v_a_2714_);
lean_inc_ref(v_a_2713_);
v___x_2851_ = lean_infer_type(v_val_2850_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v_a_2852_; lean_object* v___x_2853_; 
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
lean_inc(v_a_2852_);
lean_dec_ref(v___x_2851_);
v___x_2853_ = l_Lean_Meta_ppExpr(v_a_2852_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2878_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2856_ = v___x_2853_;
v_isShared_2857_ = v_isSharedCheck_2878_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2853_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2878_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2858_; uint8_t v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2862_; 
v___x_2858_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1));
v___x_2859_ = 1;
v___x_2860_ = l_Lean_Name_toString(v_fieldName_2849_, v___x_2859_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set_tag(v___x_2847_, 3);
lean_ctor_set(v___x_2847_, 0, v___x_2860_);
v___x_2862_ = v___x_2847_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2860_);
v___x_2862_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2875_; 
v___x_2863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2858_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
v___x_2864_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5));
v___x_2865_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2863_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
v___x_2866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
lean_ctor_set(v___x_2866_, 1, v_a_2854_);
v___x_2867_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3));
v___x_2868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2866_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
v___x_2869_ = lean_box(1);
v___x_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2868_);
lean_ctor_set(v___x_2870_, 1, v___x_2869_);
v___x_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
v___x_2872_ = lean_box(0);
v___x_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2871_);
lean_ctor_set(v___x_2873_, 1, v___x_2872_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 0, v___x_2873_);
v___x_2875_ = v___x_2856_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2873_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_dec(v_fieldName_2849_);
lean_del_object(v___x_2847_);
v_a_2879_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2853_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2853_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_dec(v_fieldName_2849_);
lean_del_object(v___x_2847_);
v_a_2887_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2851_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2851_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
}
default: 
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
lean_dec_ref(v_i_2712_);
v___x_2896_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6));
v___x_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
return v___x_2897_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___boxed(lean_object* v_i_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(v_i_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2899_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__0(lean_object* v_snd_2905_, lean_object* v_____r_2906_, lean_object* v_fmts_2907_, lean_object* v_infos_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2914_, 0, v_fmts_2907_);
lean_ctor_set(v___x_2914_, 1, v_infos_2908_);
v___x_2915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2915_, 0, v_snd_2905_);
lean_ctor_set(v___x_2915_, 1, v___x_2914_);
v___x_2916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__0___boxed(lean_object* v_snd_2917_, lean_object* v_____r_2918_, lean_object* v_fmts_2919_, lean_object* v_infos_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(v_snd_2917_, v_____r_2918_, v_fmts_2919_, v_infos_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0_spec__0(lean_object* v_x_2927_, lean_object* v_x_2928_, lean_object* v_x_2929_){
_start:
{
if (lean_obj_tag(v_x_2929_) == 0)
{
lean_dec(v_x_2927_);
return v_x_2928_;
}
else
{
lean_object* v_head_2930_; lean_object* v_tail_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2940_; 
v_head_2930_ = lean_ctor_get(v_x_2929_, 0);
v_tail_2931_ = lean_ctor_get(v_x_2929_, 1);
v_isSharedCheck_2940_ = !lean_is_exclusive(v_x_2929_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2933_ = v_x_2929_;
v_isShared_2934_ = v_isSharedCheck_2940_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_tail_2931_);
lean_inc(v_head_2930_);
lean_dec(v_x_2929_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2940_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
lean_inc(v_x_2927_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set_tag(v___x_2933_, 5);
lean_ctor_set(v___x_2933_, 1, v_x_2927_);
lean_ctor_set(v___x_2933_, 0, v_x_2928_);
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_x_2928_);
lean_ctor_set(v_reuseFailAlloc_2939_, 1, v_x_2927_);
v___x_2936_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
lean_object* v___x_2937_; 
v___x_2937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
lean_ctor_set(v___x_2937_, 1, v_head_2930_);
v_x_2928_ = v___x_2937_;
v_x_2929_ = v_tail_2931_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0(lean_object* v_x_2941_, lean_object* v_x_2942_){
_start:
{
if (lean_obj_tag(v_x_2941_) == 0)
{
lean_object* v___x_2943_; 
lean_dec(v_x_2942_);
v___x_2943_ = lean_box(0);
return v___x_2943_;
}
else
{
lean_object* v_tail_2944_; 
v_tail_2944_ = lean_ctor_get(v_x_2941_, 1);
if (lean_obj_tag(v_tail_2944_) == 0)
{
lean_object* v_head_2945_; 
lean_dec(v_x_2942_);
v_head_2945_ = lean_ctor_get(v_x_2941_, 0);
lean_inc(v_head_2945_);
lean_dec_ref(v_x_2941_);
return v_head_2945_;
}
else
{
lean_object* v_head_2946_; lean_object* v___x_2947_; 
lean_inc(v_tail_2944_);
v_head_2946_ = lean_ctor_get(v_x_2941_, 0);
lean_inc(v_head_2946_);
lean_dec_ref(v_x_2941_);
v___x_2947_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0_spec__0(v_x_2942_, v_head_2946_, v_tail_2944_);
return v___x_2947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__1(lean_object* v___x_2951_, lean_object* v_i_2952_, lean_object* v_fmts_2953_, lean_object* v_infos_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_){
_start:
{
lean_object* v___y_2961_; lean_object* v_fmts_2962_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v_fmts_2976_; lean_object* v_a_2980_; lean_object* v___y_3008_; uint8_t v___y_3009_; lean_object* v_a_3015_; lean_object* v___y_3019_; lean_object* v___x_3021_; 
lean_inc_ref(v_i_2952_);
v___x_3021_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(v_i_2952_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v_fst_3023_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref(v___x_3021_);
v_fst_3023_ = lean_ctor_get(v_a_3022_, 0);
if (lean_obj_tag(v_fst_3023_) == 1)
{
lean_object* v_val_3024_; lean_object* v_snd_3025_; lean_object* v_fmt_3026_; lean_object* v_infos_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
lean_dec(v_infos_2954_);
v_val_3024_ = lean_ctor_get(v_fst_3023_, 0);
lean_inc(v_val_3024_);
v_snd_3025_ = lean_ctor_get(v_a_3022_, 1);
lean_inc(v_snd_3025_);
lean_dec(v_a_3022_);
v_fmt_3026_ = lean_ctor_get(v_val_3024_, 0);
lean_inc(v_fmt_3026_);
v_infos_3027_ = lean_ctor_get(v_val_3024_, 1);
lean_inc(v_infos_3027_);
lean_dec(v_val_3024_);
v___x_3028_ = lean_array_push(v_fmts_2953_, v_fmt_3026_);
v___x_3029_ = lean_box(0);
v___x_3030_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(v_snd_3025_, v___x_3029_, v___x_3028_, v_infos_3027_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
v___y_3019_ = v___x_3030_;
goto v___jp_3018_;
}
else
{
lean_object* v_snd_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v_snd_3031_ = lean_ctor_get(v_a_3022_, 1);
lean_inc(v_snd_3031_);
lean_dec(v_a_3022_);
v___x_3032_ = lean_box(0);
v___x_3033_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(v_snd_3031_, v___x_3032_, v_fmts_2953_, v_infos_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
v___y_3019_ = v___x_3033_;
goto v___jp_3018_;
}
}
else
{
lean_object* v_a_3034_; 
v_a_3034_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3034_);
lean_dec_ref(v___x_3021_);
v_a_3015_ = v_a_3034_;
goto v___jp_3014_;
}
v___jp_2960_:
{
lean_object* v___x_2963_; uint8_t v___x_2964_; 
v___x_2963_ = lean_array_get_size(v_fmts_2962_);
v___x_2964_ = lean_nat_dec_eq(v___x_2963_, v___x_2951_);
if (v___x_2964_ == 0)
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2965_ = lean_array_to_list(v_fmts_2962_);
v___x_2966_ = ((lean_object*)(l_Lean_Elab_Info_fmtHover_x3f___lam__1___closed__1));
v___x_2967_ = l_Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0(v___x_2965_, v___x_2966_);
v___x_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2967_);
lean_ctor_set(v___x_2968_, 1, v___y_2961_);
v___x_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2968_);
v___x_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
return v___x_2970_;
}
else
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
lean_dec_ref(v_fmts_2962_);
lean_dec(v___y_2961_);
v___x_2971_ = lean_box(0);
v___x_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
return v___x_2972_;
}
}
v___jp_2973_:
{
if (lean_obj_tag(v___y_2974_) == 1)
{
lean_object* v_val_2977_; lean_object* v___x_2978_; 
v_val_2977_ = lean_ctor_get(v___y_2974_, 0);
lean_inc(v_val_2977_);
lean_dec_ref(v___y_2974_);
v___x_2978_ = lean_array_push(v_fmts_2976_, v_val_2977_);
v___y_2961_ = v___y_2975_;
v_fmts_2962_ = v___x_2978_;
goto v___jp_2960_;
}
else
{
lean_dec(v___y_2974_);
v___y_2961_ = v___y_2975_;
v_fmts_2962_ = v_fmts_2976_;
goto v___jp_2960_;
}
}
v___jp_2979_:
{
lean_object* v___x_2981_; 
v___x_2981_ = l_Lean_Elab_Info_docString_x3f(v_i_2952_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v_snd_2982_; lean_object* v_a_2983_; 
v_snd_2982_ = lean_ctor_get(v_a_2980_, 1);
lean_inc(v_snd_2982_);
v_a_2983_ = lean_ctor_get(v___x_2981_, 0);
lean_inc(v_a_2983_);
lean_dec_ref(v___x_2981_);
if (lean_obj_tag(v_a_2983_) == 1)
{
lean_object* v_fst_2984_; lean_object* v_fst_2985_; lean_object* v_snd_2986_; lean_object* v_val_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2995_; 
v_fst_2984_ = lean_ctor_get(v_a_2980_, 0);
lean_inc(v_fst_2984_);
lean_dec_ref(v_a_2980_);
v_fst_2985_ = lean_ctor_get(v_snd_2982_, 0);
lean_inc(v_fst_2985_);
v_snd_2986_ = lean_ctor_get(v_snd_2982_, 1);
lean_inc(v_snd_2986_);
lean_dec(v_snd_2982_);
v_val_2987_ = lean_ctor_get(v_a_2983_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v_a_2983_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2989_ = v_a_2983_;
v_isShared_2990_ = v_isSharedCheck_2995_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_val_2987_);
lean_dec(v_a_2983_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2995_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
lean_ctor_set_tag(v___x_2989_, 3);
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_val_2987_);
v___x_2992_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
lean_object* v___x_2993_; 
v___x_2993_ = lean_array_push(v_fst_2985_, v___x_2992_);
v___y_2974_ = v_fst_2984_;
v___y_2975_ = v_snd_2986_;
v_fmts_2976_ = v___x_2993_;
goto v___jp_2973_;
}
}
}
else
{
lean_object* v_fst_2996_; lean_object* v_fst_2997_; lean_object* v_snd_2998_; 
lean_dec(v_a_2983_);
v_fst_2996_ = lean_ctor_get(v_a_2980_, 0);
lean_inc(v_fst_2996_);
lean_dec_ref(v_a_2980_);
v_fst_2997_ = lean_ctor_get(v_snd_2982_, 0);
lean_inc(v_fst_2997_);
v_snd_2998_ = lean_ctor_get(v_snd_2982_, 1);
lean_inc(v_snd_2998_);
lean_dec(v_snd_2982_);
v___y_2974_ = v_fst_2996_;
v___y_2975_ = v_snd_2998_;
v_fmts_2976_ = v_fst_2997_;
goto v___jp_2973_;
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec_ref(v_a_2980_);
v_a_2999_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2981_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2981_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
v___jp_3007_:
{
if (v___y_3009_ == 0)
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
lean_dec_ref(v___y_3008_);
v___x_3010_ = lean_box(0);
v___x_3011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3011_, 0, v_fmts_2953_);
lean_ctor_set(v___x_3011_, 1, v_infos_2954_);
v___x_3012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3010_);
lean_ctor_set(v___x_3012_, 1, v___x_3011_);
v_a_2980_ = v___x_3012_;
goto v___jp_2979_;
}
else
{
lean_object* v___x_3013_; 
lean_dec(v_infos_2954_);
lean_dec_ref(v_fmts_2953_);
lean_dec_ref(v_i_2952_);
v___x_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3013_, 0, v___y_3008_);
return v___x_3013_;
}
}
v___jp_3014_:
{
uint8_t v___x_3016_; 
v___x_3016_ = l_Lean_Exception_isInterrupt(v_a_3015_);
if (v___x_3016_ == 0)
{
uint8_t v___x_3017_; 
lean_inc_ref(v_a_3015_);
v___x_3017_ = l_Lean_Exception_isRuntime(v_a_3015_);
v___y_3008_ = v_a_3015_;
v___y_3009_ = v___x_3017_;
goto v___jp_3007_;
}
else
{
v___y_3008_ = v_a_3015_;
v___y_3009_ = v___x_3016_;
goto v___jp_3007_;
}
}
v___jp_3018_:
{
lean_object* v_a_3020_; 
v_a_3020_ = lean_ctor_get(v___y_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref(v___y_3019_);
v_a_2980_ = v_a_3020_;
goto v___jp_2979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__1___boxed(lean_object* v___x_3035_, lean_object* v_i_3036_, lean_object* v_fmts_3037_, lean_object* v_infos_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_Elab_Info_fmtHover_x3f___lam__1(v___x_3035_, v_i_3036_, v_fmts_3037_, v_infos_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___x_3035_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f(lean_object* v_ci_3047_, lean_object* v_i_3048_){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v_fmts_3052_; lean_object* v_infos_3053_; lean_object* v___f_3054_; lean_object* v___x_3055_; 
v___x_3050_ = l_Lean_Elab_Info_lctx(v_i_3048_);
v___x_3051_ = lean_unsigned_to_nat(0u);
v_fmts_3052_ = ((lean_object*)(l_Lean_Elab_Info_fmtHover_x3f___closed__0));
v_infos_3053_ = lean_box(1);
v___f_3054_ = lean_alloc_closure((void*)(l_Lean_Elab_Info_fmtHover_x3f___lam__1___boxed), 9, 4);
lean_closure_set(v___f_3054_, 0, v___x_3051_);
lean_closure_set(v___f_3054_, 1, v_i_3048_);
lean_closure_set(v___f_3054_, 2, v_fmts_3052_);
lean_closure_set(v___f_3054_, 3, v_infos_3053_);
v___x_3055_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ci_3047_, v___x_3050_, v___f_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___boxed(lean_object* v_ci_3056_, lean_object* v_i_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Lean_Elab_Info_fmtHover_x3f(v_ci_3056_, v_i_3057_);
return v_res_3059_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(lean_object* v_hoverPos_3060_, lean_object* v_pos_3061_, lean_object* v_tailPos_3062_, lean_object* v_as_3063_, size_t v_i_3064_, size_t v_stop_3065_){
_start:
{
uint8_t v___x_3066_; 
v___x_3066_ = lean_usize_dec_eq(v_i_3064_, v_stop_3065_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3067_; uint8_t v___x_3068_; 
v___x_3067_ = lean_array_uget_borrowed(v_as_3063_, v_i_3064_);
v___x_3068_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(v_hoverPos_3060_, v_pos_3061_, v_tailPos_3062_, v___x_3067_);
if (v___x_3068_ == 0)
{
size_t v___x_3069_; size_t v___x_3070_; 
v___x_3069_ = ((size_t)1ULL);
v___x_3070_ = lean_usize_add(v_i_3064_, v___x_3069_);
v_i_3064_ = v___x_3070_;
goto _start;
}
else
{
return v___x_3068_;
}
}
else
{
uint8_t v___x_3072_; 
v___x_3072_ = 0;
return v___x_3072_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(lean_object* v_hoverPos_3073_, lean_object* v_pos_3074_, lean_object* v_tailPos_3075_, lean_object* v_x_3076_){
_start:
{
if (lean_obj_tag(v_x_3076_) == 0)
{
lean_object* v_cs_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; uint8_t v___x_3080_; 
v_cs_3077_ = lean_ctor_get(v_x_3076_, 0);
v___x_3078_ = lean_unsigned_to_nat(0u);
v___x_3079_ = lean_array_get_size(v_cs_3077_);
v___x_3080_ = lean_nat_dec_lt(v___x_3078_, v___x_3079_);
if (v___x_3080_ == 0)
{
return v___x_3080_;
}
else
{
if (v___x_3080_ == 0)
{
return v___x_3080_;
}
else
{
size_t v___x_3081_; size_t v___x_3082_; uint8_t v___x_3083_; 
v___x_3081_ = ((size_t)0ULL);
v___x_3082_ = lean_usize_of_nat(v___x_3079_);
v___x_3083_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(v_hoverPos_3073_, v_pos_3074_, v_tailPos_3075_, v_cs_3077_, v___x_3081_, v___x_3082_);
return v___x_3083_;
}
}
}
else
{
lean_object* v_vs_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; uint8_t v___x_3087_; 
v_vs_3084_ = lean_ctor_get(v_x_3076_, 0);
v___x_3085_ = lean_unsigned_to_nat(0u);
v___x_3086_ = lean_array_get_size(v_vs_3084_);
v___x_3087_ = lean_nat_dec_lt(v___x_3085_, v___x_3086_);
if (v___x_3087_ == 0)
{
return v___x_3087_;
}
else
{
if (v___x_3087_ == 0)
{
return v___x_3087_;
}
else
{
size_t v___x_3088_; size_t v___x_3089_; uint8_t v___x_3090_; 
v___x_3088_ = ((size_t)0ULL);
v___x_3089_ = lean_usize_of_nat(v___x_3086_);
v___x_3090_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_3073_, v_pos_3074_, v_tailPos_3075_, v_vs_3084_, v___x_3088_, v___x_3089_);
return v___x_3090_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(lean_object* v_hoverPos_3091_, lean_object* v_pos_3092_, lean_object* v_tailPos_3093_, lean_object* v_t_3094_){
_start:
{
lean_object* v_root_3095_; lean_object* v_tail_3096_; uint8_t v___x_3097_; 
v_root_3095_ = lean_ctor_get(v_t_3094_, 0);
v_tail_3096_ = lean_ctor_get(v_t_3094_, 1);
v___x_3097_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(v_hoverPos_3091_, v_pos_3092_, v_tailPos_3093_, v_root_3095_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
v___x_3098_ = lean_unsigned_to_nat(0u);
v___x_3099_ = lean_array_get_size(v_tail_3096_);
v___x_3100_ = lean_nat_dec_lt(v___x_3098_, v___x_3099_);
if (v___x_3100_ == 0)
{
return v___x_3097_;
}
else
{
if (v___x_3100_ == 0)
{
return v___x_3097_;
}
else
{
size_t v___x_3101_; size_t v___x_3102_; uint8_t v___x_3103_; 
v___x_3101_ = ((size_t)0ULL);
v___x_3102_ = lean_usize_of_nat(v___x_3099_);
v___x_3103_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_3091_, v_pos_3092_, v_tailPos_3093_, v_tail_3096_, v___x_3101_, v___x_3102_);
return v___x_3103_;
}
}
}
else
{
return v___x_3097_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(lean_object* v_hoverPos_3112_, lean_object* v_pos_3113_, lean_object* v_tailPos_3114_, lean_object* v_a_3115_){
_start:
{
if (lean_obj_tag(v_a_3115_) == 1)
{
lean_object* v_i_3116_; lean_object* v_children_3117_; uint8_t v___y_3119_; 
v_i_3116_ = lean_ctor_get(v_a_3115_, 0);
v_children_3117_ = lean_ctor_get(v_a_3115_, 1);
switch(lean_obj_tag(v_i_3116_))
{
case 0:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; uint8_t v___x_3123_; 
v___x_3121_ = l_Lean_Elab_Info_stx(v_i_3116_);
v___x_3122_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3));
v___x_3123_ = l_Lean_Syntax_isOfKind(v___x_3121_, v___x_3122_);
if (v___x_3123_ == 0)
{
lean_object* v___x_3124_; 
v___x_3124_ = l_Lean_Elab_Info_pos_x3f(v_i_3116_);
if (lean_obj_tag(v___x_3124_) == 1)
{
lean_object* v_val_3125_; lean_object* v___x_3126_; 
v_val_3125_ = lean_ctor_get(v___x_3124_, 0);
lean_inc(v_val_3125_);
lean_dec_ref(v___x_3124_);
v___x_3126_ = l_Lean_Elab_Info_tailPos_x3f(v_i_3116_);
if (lean_obj_tag(v___x_3126_) == 1)
{
lean_object* v_val_3127_; uint8_t v___x_3128_; uint8_t v___y_3130_; 
v_val_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_val_3127_);
lean_dec_ref(v___x_3126_);
v___x_3128_ = lean_nat_dec_lt(v_hoverPos_3112_, v_val_3127_);
if (v___x_3128_ == 0)
{
lean_dec(v_val_3127_);
lean_dec(v_val_3125_);
v___y_3119_ = v___x_3128_;
goto v___jp_3118_;
}
else
{
uint8_t v___x_3131_; 
v___x_3131_ = lean_nat_dec_eq(v_val_3125_, v_pos_3113_);
lean_dec(v_val_3125_);
if (v___x_3131_ == 0)
{
lean_dec(v_val_3127_);
v___y_3130_ = v___x_3131_;
goto v___jp_3129_;
}
else
{
uint8_t v___x_3132_; 
v___x_3132_ = lean_nat_dec_eq(v_val_3127_, v_tailPos_3114_);
lean_dec(v_val_3127_);
v___y_3130_ = v___x_3132_;
goto v___jp_3129_;
}
}
v___jp_3129_:
{
if (v___y_3130_ == 0)
{
v___y_3119_ = v___x_3128_;
goto v___jp_3118_;
}
else
{
v___y_3119_ = v___x_3123_;
goto v___jp_3118_;
}
}
}
else
{
uint8_t v___x_3133_; 
lean_dec(v___x_3126_);
lean_dec(v_val_3125_);
v___x_3133_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_3112_, v_pos_3113_, v_tailPos_3114_, v_children_3117_);
return v___x_3133_;
}
}
else
{
uint8_t v___x_3134_; 
lean_dec(v___x_3124_);
v___x_3134_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_3112_, v_pos_3113_, v_tailPos_3114_, v_children_3117_);
return v___x_3134_;
}
}
else
{
uint8_t v___x_3135_; 
v___x_3135_ = 0;
return v___x_3135_;
}
}
case 4:
{
uint8_t v___x_3136_; 
v___x_3136_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_3112_, v_pos_3113_, v_tailPos_3114_, v_children_3117_);
return v___x_3136_;
}
default: 
{
uint8_t v___x_3137_; 
v___x_3137_ = 0;
return v___x_3137_;
}
}
v___jp_3118_:
{
if (v___y_3119_ == 0)
{
uint8_t v___x_3120_; 
v___x_3120_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_3112_, v_pos_3113_, v_tailPos_3114_, v_children_3117_);
return v___x_3120_;
}
else
{
return v___y_3119_;
}
}
}
else
{
uint8_t v___x_3138_; 
v___x_3138_ = 0;
return v___x_3138_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(lean_object* v_hoverPos_3139_, lean_object* v_pos_3140_, lean_object* v_tailPos_3141_, lean_object* v_as_3142_, size_t v_i_3143_, size_t v_stop_3144_){
_start:
{
uint8_t v___x_3145_; 
v___x_3145_ = lean_usize_dec_eq(v_i_3143_, v_stop_3144_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3146_; uint8_t v___x_3147_; 
v___x_3146_ = lean_array_uget_borrowed(v_as_3142_, v_i_3143_);
v___x_3147_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(v_hoverPos_3139_, v_pos_3140_, v_tailPos_3141_, v___x_3146_);
if (v___x_3147_ == 0)
{
size_t v___x_3148_; size_t v___x_3149_; 
v___x_3148_ = ((size_t)1ULL);
v___x_3149_ = lean_usize_add(v_i_3143_, v___x_3148_);
v_i_3143_ = v___x_3149_;
goto _start;
}
else
{
return v___x_3147_;
}
}
else
{
uint8_t v___x_3151_; 
v___x_3151_ = 0;
return v___x_3151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1___boxed(lean_object* v_hoverPos_3152_, lean_object* v_pos_3153_, lean_object* v_tailPos_3154_, lean_object* v_as_3155_, lean_object* v_i_3156_, lean_object* v_stop_3157_){
_start:
{
size_t v_i_boxed_3158_; size_t v_stop_boxed_3159_; uint8_t v_res_3160_; lean_object* v_r_3161_; 
v_i_boxed_3158_ = lean_unbox_usize(v_i_3156_);
lean_dec(v_i_3156_);
v_stop_boxed_3159_ = lean_unbox_usize(v_stop_3157_);
lean_dec(v_stop_3157_);
v_res_3160_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_3152_, v_pos_3153_, v_tailPos_3154_, v_as_3155_, v_i_boxed_3158_, v_stop_boxed_3159_);
lean_dec_ref(v_as_3155_);
lean_dec(v_tailPos_3154_);
lean_dec(v_pos_3153_);
lean_dec(v_hoverPos_3152_);
v_r_3161_ = lean_box(v_res_3160_);
return v_r_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1___boxed(lean_object* v_hoverPos_3162_, lean_object* v_pos_3163_, lean_object* v_tailPos_3164_, lean_object* v_as_3165_, lean_object* v_i_3166_, lean_object* v_stop_3167_){
_start:
{
size_t v_i_boxed_3168_; size_t v_stop_boxed_3169_; uint8_t v_res_3170_; lean_object* v_r_3171_; 
v_i_boxed_3168_ = lean_unbox_usize(v_i_3166_);
lean_dec(v_i_3166_);
v_stop_boxed_3169_ = lean_unbox_usize(v_stop_3167_);
lean_dec(v_stop_3167_);
v_res_3170_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(v_hoverPos_3162_, v_pos_3163_, v_tailPos_3164_, v_as_3165_, v_i_boxed_3168_, v_stop_boxed_3169_);
lean_dec_ref(v_as_3165_);
lean_dec(v_tailPos_3164_);
lean_dec(v_pos_3163_);
lean_dec(v_hoverPos_3162_);
v_r_3171_ = lean_box(v_res_3170_);
return v_r_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0___boxed(lean_object* v_hoverPos_3172_, lean_object* v_pos_3173_, lean_object* v_tailPos_3174_, lean_object* v_t_3175_){
_start:
{
uint8_t v_res_3176_; lean_object* v_r_3177_; 
v_res_3176_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_3172_, v_pos_3173_, v_tailPos_3174_, v_t_3175_);
lean_dec_ref(v_t_3175_);
lean_dec(v_tailPos_3174_);
lean_dec(v_pos_3173_);
lean_dec(v_hoverPos_3172_);
v_r_3177_ = lean_box(v_res_3176_);
return v_r_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0___boxed(lean_object* v_hoverPos_3178_, lean_object* v_pos_3179_, lean_object* v_tailPos_3180_, lean_object* v_x_3181_){
_start:
{
uint8_t v_res_3182_; lean_object* v_r_3183_; 
v_res_3182_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(v_hoverPos_3178_, v_pos_3179_, v_tailPos_3180_, v_x_3181_);
lean_dec_ref(v_x_3181_);
lean_dec(v_tailPos_3180_);
lean_dec(v_pos_3179_);
lean_dec(v_hoverPos_3178_);
v_r_3183_ = lean_box(v_res_3182_);
return v_r_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___boxed(lean_object* v_hoverPos_3184_, lean_object* v_pos_3185_, lean_object* v_tailPos_3186_, lean_object* v_a_3187_){
_start:
{
uint8_t v_res_3188_; lean_object* v_r_3189_; 
v_res_3188_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(v_hoverPos_3184_, v_pos_3185_, v_tailPos_3186_, v_a_3187_);
lean_dec_ref(v_a_3187_);
lean_dec(v_tailPos_3186_);
lean_dec(v_pos_3185_);
lean_dec(v_hoverPos_3184_);
v_r_3189_ = lean_box(v_res_3188_);
return v_r_3189_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2(lean_object* v_x_3190_, lean_object* v_x_3191_){
_start:
{
if (lean_obj_tag(v_x_3190_) == 0)
{
if (lean_obj_tag(v_x_3191_) == 0)
{
uint8_t v___x_3192_; 
v___x_3192_ = 1;
return v___x_3192_;
}
else
{
uint8_t v___x_3193_; 
v___x_3193_ = 0;
return v___x_3193_;
}
}
else
{
if (lean_obj_tag(v_x_3191_) == 0)
{
uint8_t v___x_3194_; 
v___x_3194_ = 0;
return v___x_3194_;
}
else
{
lean_object* v_val_3195_; lean_object* v_val_3196_; uint8_t v___x_3197_; 
v_val_3195_ = lean_ctor_get(v_x_3190_, 0);
v_val_3196_ = lean_ctor_get(v_x_3191_, 0);
v___x_3197_ = lean_nat_dec_eq(v_val_3195_, v_val_3196_);
return v___x_3197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2___boxed(lean_object* v_x_3198_, lean_object* v_x_3199_){
_start:
{
uint8_t v_res_3200_; lean_object* v_r_3201_; 
v_res_3200_ = l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2(v_x_3198_, v_x_3199_);
lean_dec(v_x_3199_);
lean_dec(v_x_3198_);
v_r_3201_ = lean_box(v_res_3200_);
return v_r_3201_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0(lean_object* v_x_3202_){
_start:
{
uint8_t v_indented_3203_; 
v_indented_3203_ = lean_ctor_get_uint8(v_x_3202_, sizeof(void*)*3 + 1);
return v_indented_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0___boxed(lean_object* v_x_3204_){
_start:
{
uint8_t v_res_3205_; lean_object* v_r_3206_; 
v_res_3205_ = l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0(v_x_3204_);
lean_dec_ref(v_x_3204_);
v_r_3206_ = lean_box(v_res_3205_);
return v_r_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f___lam__1(lean_object* v_text_3207_, lean_object* v_hoverPos_3208_, lean_object* v___f_3209_, lean_object* v_ctx_3210_, lean_object* v_i_3211_, lean_object* v_cs_3212_, lean_object* v_gs_3213_){
_start:
{
if (lean_obj_tag(v_i_3211_) == 0)
{
lean_object* v_i_3214_; uint8_t v___y_3216_; uint8_t v___y_3217_; lean_object* v___y_3218_; lean_object* v___x_3222_; 
v_i_3214_ = lean_ctor_get(v_i_3211_, 0);
v___x_3222_ = l_Lean_Elab_Info_pos_x3f(v_i_3211_);
if (lean_obj_tag(v___x_3222_) == 1)
{
lean_object* v_val_3223_; lean_object* v___x_3224_; 
v_val_3223_ = lean_ctor_get(v___x_3222_, 0);
lean_inc(v_val_3223_);
lean_dec_ref(v___x_3222_);
v___x_3224_ = l_Lean_Elab_Info_tailPos_x3f(v_i_3211_);
if (lean_obj_tag(v___x_3224_) == 1)
{
lean_object* v_val_3225_; lean_object* v_source_3226_; uint8_t v___x_3227_; 
v_val_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_val_3225_);
lean_dec_ref(v___x_3224_);
v_source_3226_ = lean_ctor_get(v_text_3207_, 0);
v___x_3227_ = lean_nat_dec_le(v_val_3223_, v_hoverPos_3208_);
if (v___x_3227_ == 0)
{
lean_dec(v_val_3225_);
lean_dec(v_val_3223_);
lean_dec_ref(v_ctx_3210_);
lean_dec_ref(v___f_3209_);
lean_dec_ref(v_text_3207_);
return v_gs_3213_;
}
else
{
lean_object* v___x_3228_; lean_object* v_trailSize_3229_; lean_object* v___x_3230_; uint8_t v___y_3232_; uint8_t v___y_3242_; uint8_t v___y_3247_; lean_object* v___x_3251_; uint8_t v_atEOF_3252_; lean_object* v___y_3254_; lean_object* v___x_3257_; uint8_t v___x_3258_; 
v___x_3228_ = l_Lean_Elab_Info_stx(v_i_3211_);
v_trailSize_3229_ = l_Lean_Syntax_getTrailingSize(v___x_3228_);
lean_dec(v___x_3228_);
v___x_3230_ = lean_nat_add(v_val_3225_, v_trailSize_3229_);
v___x_3251_ = lean_string_utf8_byte_size(v_source_3226_);
v_atEOF_3252_ = lean_nat_dec_eq(v___x_3230_, v___x_3251_);
v___x_3257_ = lean_unsigned_to_nat(1u);
v___x_3258_ = lean_nat_dec_le(v___x_3257_, v_trailSize_3229_);
if (v___x_3258_ == 0)
{
lean_dec(v_trailSize_3229_);
v___y_3254_ = v___x_3257_;
goto v___jp_3253_;
}
else
{
v___y_3254_ = v_trailSize_3229_;
goto v___jp_3253_;
}
v___jp_3231_:
{
lean_object* v___x_3233_; lean_object* v_column_3234_; lean_object* v___x_3235_; lean_object* v_column_3236_; uint8_t v___x_3237_; uint8_t v___x_3238_; 
lean_inc_ref(v_text_3207_);
v___x_3233_ = l_Lean_FileMap_toPosition(v_text_3207_, v_hoverPos_3208_);
v_column_3234_ = lean_ctor_get(v___x_3233_, 1);
lean_inc(v_column_3234_);
lean_dec_ref(v___x_3233_);
v___x_3235_ = l_Lean_FileMap_toPosition(v_text_3207_, v_val_3223_);
lean_dec(v_val_3223_);
v_column_3236_ = lean_ctor_get(v___x_3235_, 1);
lean_inc(v_column_3236_);
lean_dec_ref(v___x_3235_);
v___x_3237_ = lean_nat_dec_lt(v_column_3234_, v_column_3236_);
lean_dec(v_column_3236_);
lean_dec(v_column_3234_);
v___x_3238_ = lean_nat_dec_eq(v_hoverPos_3208_, v___x_3230_);
lean_dec(v___x_3230_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; 
v___x_3239_ = lean_unsigned_to_nat(1u);
v___y_3216_ = v___x_3237_;
v___y_3217_ = v___y_3232_;
v___y_3218_ = v___x_3239_;
goto v___jp_3215_;
}
else
{
lean_object* v___x_3240_; 
v___x_3240_ = lean_unsigned_to_nat(0u);
v___y_3216_ = v___x_3237_;
v___y_3217_ = v___y_3232_;
v___y_3218_ = v___x_3240_;
goto v___jp_3215_;
}
}
v___jp_3241_:
{
if (v___y_3242_ == 0)
{
lean_dec(v___x_3230_);
lean_dec(v_val_3225_);
lean_dec(v_val_3223_);
lean_dec_ref(v_ctx_3210_);
lean_dec_ref(v_text_3207_);
return v_gs_3213_;
}
else
{
uint8_t v___x_3243_; 
lean_dec(v_gs_3213_);
v___x_3243_ = lean_nat_dec_lt(v_val_3223_, v_hoverPos_3208_);
if (v___x_3243_ == 0)
{
lean_dec(v_val_3225_);
v___y_3232_ = v___x_3243_;
goto v___jp_3231_;
}
else
{
uint8_t v___x_3244_; 
v___x_3244_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_3208_, v_val_3223_, v_val_3225_, v_cs_3212_);
lean_dec(v_val_3225_);
if (v___x_3244_ == 0)
{
v___y_3232_ = v___x_3243_;
goto v___jp_3231_;
}
else
{
uint8_t v___x_3245_; 
v___x_3245_ = 0;
v___y_3232_ = v___x_3245_;
goto v___jp_3231_;
}
}
}
}
v___jp_3246_:
{
if (v___y_3247_ == 0)
{
lean_dec(v___x_3230_);
lean_dec(v_val_3225_);
lean_dec(v_val_3223_);
lean_dec_ref(v_ctx_3210_);
lean_dec_ref(v___f_3209_);
lean_dec_ref(v_text_3207_);
return v_gs_3213_;
}
else
{
uint8_t v___x_3248_; 
v___x_3248_ = l_List_isEmpty___redArg(v_gs_3213_);
if (v___x_3248_ == 0)
{
uint8_t v___x_3249_; 
v___x_3249_ = lean_nat_dec_le(v_val_3225_, v_hoverPos_3208_);
if (v___x_3249_ == 0)
{
lean_dec_ref(v___f_3209_);
v___y_3242_ = v___x_3249_;
goto v___jp_3241_;
}
else
{
uint8_t v___x_3250_; 
lean_inc(v_gs_3213_);
v___x_3250_ = l_List_all___redArg(v_gs_3213_, v___f_3209_);
v___y_3242_ = v___x_3250_;
goto v___jp_3241_;
}
}
else
{
lean_dec_ref(v___f_3209_);
v___y_3242_ = v___x_3248_;
goto v___jp_3241_;
}
}
}
v___jp_3253_:
{
lean_object* v___x_3255_; uint8_t v___x_3256_; 
v___x_3255_ = lean_nat_add(v_val_3225_, v___y_3254_);
lean_dec(v___y_3254_);
v___x_3256_ = lean_nat_dec_lt(v_hoverPos_3208_, v___x_3255_);
lean_dec(v___x_3255_);
if (v___x_3256_ == 0)
{
v___y_3247_ = v_atEOF_3252_;
goto v___jp_3246_;
}
else
{
v___y_3247_ = v___x_3256_;
goto v___jp_3246_;
}
}
}
}
else
{
lean_dec(v___x_3224_);
lean_dec(v_val_3223_);
lean_dec_ref(v_ctx_3210_);
lean_dec_ref(v___f_3209_);
lean_dec_ref(v_text_3207_);
return v_gs_3213_;
}
}
else
{
lean_dec(v___x_3222_);
lean_dec_ref(v_ctx_3210_);
lean_dec_ref(v___f_3209_);
lean_dec_ref(v_text_3207_);
return v_gs_3213_;
}
v___jp_3215_:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
lean_inc_ref(v_i_3214_);
v___x_3219_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3219_, 0, v_ctx_3210_);
lean_ctor_set(v___x_3219_, 1, v_i_3214_);
lean_ctor_set(v___x_3219_, 2, v___y_3218_);
lean_ctor_set_uint8(v___x_3219_, sizeof(void*)*3, v___y_3217_);
lean_ctor_set_uint8(v___x_3219_, sizeof(void*)*3 + 1, v___y_3216_);
v___x_3220_ = lean_box(0);
v___x_3221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3219_);
lean_ctor_set(v___x_3221_, 1, v___x_3220_);
return v___x_3221_;
}
}
else
{
lean_dec_ref(v_ctx_3210_);
lean_dec_ref(v___f_3209_);
lean_dec_ref(v_text_3207_);
return v_gs_3213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f___lam__1___boxed(lean_object* v_text_3259_, lean_object* v_hoverPos_3260_, lean_object* v___f_3261_, lean_object* v_ctx_3262_, lean_object* v_i_3263_, lean_object* v_cs_3264_, lean_object* v_gs_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l_Lean_Elab_InfoTree_goalsAt_x3f___lam__1(v_text_3259_, v_hoverPos_3260_, v___f_3261_, v_ctx_3262_, v_i_3263_, v_cs_3264_, v_gs_3265_);
lean_dec_ref(v_cs_3264_);
lean_dec_ref(v_i_3263_);
lean_dec(v_hoverPos_3260_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(lean_object* v_a_3267_, lean_object* v_a_3268_){
_start:
{
if (lean_obj_tag(v_a_3267_) == 0)
{
lean_object* v___x_3269_; 
v___x_3269_ = l_List_reverse___redArg(v_a_3268_);
return v___x_3269_;
}
else
{
lean_object* v_head_3270_; lean_object* v_tail_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3280_; 
v_head_3270_ = lean_ctor_get(v_a_3267_, 0);
v_tail_3271_ = lean_ctor_get(v_a_3267_, 1);
v_isSharedCheck_3280_ = !lean_is_exclusive(v_a_3267_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3273_ = v_a_3267_;
v_isShared_3274_ = v_isSharedCheck_3280_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_tail_3271_);
lean_inc(v_head_3270_);
lean_dec(v_a_3267_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3280_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v_priority_3275_; lean_object* v___x_3277_; 
v_priority_3275_ = lean_ctor_get(v_head_3270_, 2);
lean_inc(v_priority_3275_);
lean_dec(v_head_3270_);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 1, v_a_3268_);
lean_ctor_set(v___x_3273_, 0, v_priority_3275_);
v___x_3277_ = v___x_3273_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_priority_3275_);
lean_ctor_set(v_reuseFailAlloc_3279_, 1, v_a_3268_);
v___x_3277_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
v_a_3267_ = v_tail_3271_;
v_a_3268_ = v___x_3277_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1_spec__1(lean_object* v_x_3281_, lean_object* v_x_3282_){
_start:
{
if (lean_obj_tag(v_x_3282_) == 0)
{
lean_inc(v_x_3281_);
return v_x_3281_;
}
else
{
lean_object* v_head_3283_; lean_object* v_tail_3284_; uint8_t v___x_3285_; 
v_head_3283_ = lean_ctor_get(v_x_3282_, 0);
v_tail_3284_ = lean_ctor_get(v_x_3282_, 1);
v___x_3285_ = lean_nat_dec_le(v_x_3281_, v_head_3283_);
if (v___x_3285_ == 0)
{
v_x_3282_ = v_tail_3284_;
goto _start;
}
else
{
v_x_3281_ = v_head_3283_;
v_x_3282_ = v_tail_3284_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1_spec__1___boxed(lean_object* v_x_3288_, lean_object* v_x_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1_spec__1(v_x_3288_, v_x_3289_);
lean_dec(v_x_3289_);
lean_dec(v_x_3288_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(lean_object* v_x_3291_){
_start:
{
if (lean_obj_tag(v_x_3291_) == 0)
{
lean_object* v___x_3292_; 
v___x_3292_ = lean_box(0);
return v___x_3292_;
}
else
{
lean_object* v_head_3293_; lean_object* v_tail_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v_head_3293_ = lean_ctor_get(v_x_3291_, 0);
v_tail_3294_ = lean_ctor_get(v_x_3291_, 1);
v___x_3295_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1_spec__1(v_head_3293_, v_tail_3294_);
v___x_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3295_);
return v___x_3296_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1___boxed(lean_object* v_x_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(v_x_3297_);
lean_dec(v_x_3297_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(lean_object* v_maxPrio_x3f_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_){
_start:
{
if (lean_obj_tag(v_a_3300_) == 0)
{
lean_object* v___x_3302_; 
v___x_3302_ = l_List_reverse___redArg(v_a_3301_);
return v___x_3302_;
}
else
{
lean_object* v_head_3303_; lean_object* v_tail_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3316_; 
v_head_3303_ = lean_ctor_get(v_a_3300_, 0);
v_tail_3304_ = lean_ctor_get(v_a_3300_, 1);
v_isSharedCheck_3316_ = !lean_is_exclusive(v_a_3300_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3306_ = v_a_3300_;
v_isShared_3307_ = v_isSharedCheck_3316_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_tail_3304_);
lean_inc(v_head_3303_);
lean_dec(v_a_3300_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3316_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v_priority_3308_; lean_object* v___x_3309_; uint8_t v___x_3310_; 
v_priority_3308_ = lean_ctor_get(v_head_3303_, 2);
lean_inc(v_priority_3308_);
v___x_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3309_, 0, v_priority_3308_);
v___x_3310_ = l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2(v___x_3309_, v_maxPrio_x3f_3299_);
lean_dec_ref(v___x_3309_);
if (v___x_3310_ == 0)
{
lean_del_object(v___x_3306_);
lean_dec(v_head_3303_);
v_a_3300_ = v_tail_3304_;
goto _start;
}
else
{
lean_object* v___x_3313_; 
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 1, v_a_3301_);
v___x_3313_ = v___x_3306_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_head_3303_);
lean_ctor_set(v_reuseFailAlloc_3315_, 1, v_a_3301_);
v___x_3313_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
v_a_3300_ = v_tail_3304_;
v_a_3301_ = v___x_3313_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3___boxed(lean_object* v_maxPrio_x3f_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(v_maxPrio_x3f_3317_, v_a_3318_, v_a_3319_);
lean_dec(v_maxPrio_x3f_3317_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f(lean_object* v_text_3322_, lean_object* v_t_3323_, lean_object* v_hoverPos_3324_){
_start:
{
lean_object* v___f_3325_; lean_object* v___f_3326_; lean_object* v_gs_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v_maxPrio_x3f_3330_; lean_object* v___x_3331_; 
v___f_3325_ = ((lean_object*)(l_Lean_Elab_InfoTree_goalsAt_x3f___closed__0));
v___f_3326_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_goalsAt_x3f___lam__1___boxed), 7, 3);
lean_closure_set(v___f_3326_, 0, v_text_3322_);
lean_closure_set(v___f_3326_, 1, v_hoverPos_3324_);
lean_closure_set(v___f_3326_, 2, v___f_3325_);
v_gs_3327_ = l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg(v___f_3326_, v_t_3323_);
v___x_3328_ = lean_box(0);
lean_inc(v_gs_3327_);
v___x_3329_ = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(v_gs_3327_, v___x_3328_);
v_maxPrio_x3f_3330_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(v___x_3329_);
lean_dec(v___x_3329_);
v___x_3331_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(v_maxPrio_x3f_3330_, v_gs_3327_, v___x_3328_);
lean_dec(v_maxPrio_x3f_3330_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(lean_object* v___x_3332_, uint8_t v___y_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_){
_start:
{
if (lean_obj_tag(v_a_3334_) == 0)
{
lean_object* v___x_3336_; 
v___x_3336_ = l_List_reverse___redArg(v_a_3335_);
return v___x_3336_;
}
else
{
lean_object* v_head_3337_; lean_object* v_snd_3338_; lean_object* v_tail_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3354_; 
v_head_3337_ = lean_ctor_get(v_a_3334_, 0);
lean_inc(v_head_3337_);
v_snd_3338_ = lean_ctor_get(v_head_3337_, 1);
v_tail_3339_ = lean_ctor_get(v_a_3334_, 1);
v_isSharedCheck_3354_ = !lean_is_exclusive(v_a_3334_);
if (v_isSharedCheck_3354_ == 0)
{
lean_object* v_unused_3355_; 
v_unused_3355_ = lean_ctor_get(v_a_3334_, 0);
lean_dec(v_unused_3355_);
v___x_3341_ = v_a_3334_;
v_isShared_3342_ = v_isSharedCheck_3354_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_tail_3339_);
lean_dec(v_a_3334_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3354_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v_info_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; uint8_t v___x_3347_; 
v_info_3343_ = lean_ctor_get(v_snd_3338_, 1);
v___x_3344_ = l_Lean_Elab_Info_stx(v_info_3343_);
v___x_3345_ = lean_unsigned_to_nat(0u);
v___x_3346_ = l_Lean_Syntax_getArg(v___x_3332_, v___x_3345_);
v___x_3347_ = l_Lean_Syntax_structEq(v___x_3344_, v___x_3346_);
if (v___x_3347_ == 0)
{
if (v___y_3333_ == 0)
{
lean_del_object(v___x_3341_);
lean_dec(v_head_3337_);
v_a_3334_ = v_tail_3339_;
goto _start;
}
else
{
lean_object* v___x_3350_; 
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 1, v_a_3335_);
v___x_3350_ = v___x_3341_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_head_3337_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v_a_3335_);
v___x_3350_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
v_a_3334_ = v_tail_3339_;
v_a_3335_ = v___x_3350_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_3341_);
lean_dec(v_head_3337_);
v_a_3334_ = v_tail_3339_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0___boxed(lean_object* v___x_3356_, lean_object* v___y_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_){
_start:
{
uint8_t v___y_1103__boxed_3360_; lean_object* v_res_3361_; 
v___y_1103__boxed_3360_ = lean_unbox(v___y_3357_);
v_res_3361_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(v___x_3356_, v___y_1103__boxed_3360_, v_a_3358_, v_a_3359_);
lean_dec(v___x_3356_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0(lean_object* v_ctx_3368_, lean_object* v_info_3369_, lean_object* v_children_3370_, lean_object* v_results_3371_){
_start:
{
lean_object* v___x_3372_; uint8_t v___y_3374_; lean_object* v___x_3377_; uint8_t v___x_3378_; 
v___x_3372_ = l_Lean_Elab_Info_stx(v_info_3369_);
v___x_3377_ = ((lean_object*)(l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1));
lean_inc(v___x_3372_);
v___x_3378_ = l_Lean_Syntax_isOfKind(v___x_3372_, v___x_3377_);
if (v___x_3378_ == 0)
{
v___y_3374_ = v___x_3378_;
goto v___jp_3373_;
}
else
{
lean_object* v___x_3379_; lean_object* v___x_3380_; uint8_t v___x_3381_; 
v___x_3379_ = lean_unsigned_to_nat(0u);
v___x_3380_ = l_Lean_Syntax_getArg(v___x_3372_, v___x_3379_);
v___x_3381_ = l_Lean_Syntax_isIdent(v___x_3380_);
lean_dec(v___x_3380_);
v___y_3374_ = v___x_3381_;
goto v___jp_3373_;
}
v___jp_3373_:
{
if (v___y_3374_ == 0)
{
lean_dec(v___x_3372_);
return v_results_3371_;
}
else
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = lean_box(0);
v___x_3376_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(v___x_3372_, v___y_3374_, v_results_3371_, v___x_3375_);
lean_dec(v___x_3372_);
return v___x_3376_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___boxed(lean_object* v_ctx_3382_, lean_object* v_info_3383_, lean_object* v_children_3384_, lean_object* v_results_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0(v_ctx_3382_, v_info_3383_, v_children_3384_, v_results_3385_);
lean_dec_ref(v_children_3384_);
lean_dec_ref(v_info_3383_);
lean_dec_ref(v_ctx_3382_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(lean_object* v_x_3387_, lean_object* v_x_3388_){
_start:
{
if (lean_obj_tag(v_x_3388_) == 0)
{
lean_inc_ref(v_x_3387_);
return v_x_3387_;
}
else
{
lean_object* v_head_3389_; lean_object* v_tail_3390_; uint8_t v___x_3391_; 
v_head_3389_ = lean_ctor_get(v_x_3388_, 0);
v_tail_3390_ = lean_ctor_get(v_x_3388_, 1);
v___x_3391_ = l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(v_x_3387_, v_head_3389_);
if (v___x_3391_ == 2)
{
v_x_3388_ = v_tail_3390_;
goto _start;
}
else
{
v_x_3387_ = v_head_3389_;
v_x_3388_ = v_tail_3390_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4___boxed(lean_object* v_x_3394_, lean_object* v_x_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(v_x_3394_, v_x_3395_);
lean_dec(v_x_3395_);
lean_dec_ref(v_x_3394_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(lean_object* v_x_3397_){
_start:
{
if (lean_obj_tag(v_x_3397_) == 0)
{
lean_object* v___x_3398_; 
v___x_3398_ = lean_box(0);
return v___x_3398_;
}
else
{
lean_object* v_head_3399_; lean_object* v_tail_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v_head_3399_ = lean_ctor_get(v_x_3397_, 0);
v_tail_3400_ = lean_ctor_get(v_x_3397_, 1);
v___x_3401_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(v_head_3399_, v_tail_3400_);
v___x_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
return v___x_3402_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3___boxed(lean_object* v_x_3403_){
_start:
{
lean_object* v_res_3404_; 
v_res_3404_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(v_x_3403_);
lean_dec(v_x_3403_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__1(lean_object* v_a_3405_, lean_object* v_a_3406_){
_start:
{
if (lean_obj_tag(v_a_3405_) == 0)
{
lean_object* v___x_3407_; 
v___x_3407_ = lean_array_to_list(v_a_3406_);
return v___x_3407_;
}
else
{
lean_object* v_head_3408_; 
v_head_3408_ = lean_ctor_get(v_a_3405_, 0);
if (lean_obj_tag(v_head_3408_) == 0)
{
lean_object* v_tail_3409_; 
v_tail_3409_ = lean_ctor_get(v_a_3405_, 1);
lean_inc(v_tail_3409_);
lean_dec_ref(v_a_3405_);
v_a_3405_ = v_tail_3409_;
goto _start;
}
else
{
lean_object* v_val_3411_; 
v_val_3411_ = lean_ctor_get(v_head_3408_, 0);
if (lean_obj_tag(v_val_3411_) == 0)
{
lean_object* v_tail_3412_; 
v_tail_3412_ = lean_ctor_get(v_a_3405_, 1);
lean_inc(v_tail_3412_);
lean_dec_ref(v_a_3405_);
v_a_3405_ = v_tail_3412_;
goto _start;
}
else
{
lean_object* v_tail_3414_; lean_object* v_val_3415_; lean_object* v___x_3416_; 
lean_inc_ref(v_val_3411_);
v_tail_3414_ = lean_ctor_get(v_a_3405_, 1);
lean_inc(v_tail_3414_);
lean_dec_ref(v_a_3405_);
v_val_3415_ = lean_ctor_get(v_val_3411_, 0);
lean_inc(v_val_3415_);
lean_dec_ref(v_val_3411_);
v___x_3416_ = lean_array_push(v_a_3406_, v_val_3415_);
v_a_3405_ = v_tail_3414_;
v_a_3406_ = v___x_3416_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(lean_object* v_x_3418_, lean_object* v_x_3419_){
_start:
{
if (lean_obj_tag(v_x_3418_) == 0)
{
if (lean_obj_tag(v_x_3419_) == 0)
{
uint8_t v___x_3420_; 
v___x_3420_ = 1;
return v___x_3420_;
}
else
{
uint8_t v___x_3421_; 
v___x_3421_ = 0;
return v___x_3421_;
}
}
else
{
if (lean_obj_tag(v_x_3419_) == 0)
{
uint8_t v___x_3422_; 
v___x_3422_ = 0;
return v___x_3422_;
}
else
{
lean_object* v_val_3423_; lean_object* v_val_3424_; uint8_t v___x_3425_; 
v_val_3423_ = lean_ctor_get(v_x_3418_, 0);
v_val_3424_ = lean_ctor_get(v_x_3419_, 0);
v___x_3425_ = l_Lean_Elab_instBEqHoverableInfoPrio_beq(v_val_3423_, v_val_3424_);
return v___x_3425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4___boxed(lean_object* v_x_3426_, lean_object* v_x_3427_){
_start:
{
uint8_t v_res_3428_; lean_object* v_r_3429_; 
v_res_3428_ = l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(v_x_3426_, v_x_3427_);
lean_dec(v_x_3427_);
lean_dec(v_x_3426_);
v_r_3429_ = lean_box(v_res_3428_);
return v_r_3429_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1(lean_object* v_maxPrio_x3f_3430_, lean_object* v_x_3431_){
_start:
{
lean_object* v_fst_3432_; lean_object* v___x_3433_; uint8_t v___x_3434_; 
v_fst_3432_ = lean_ctor_get(v_x_3431_, 0);
lean_inc(v_fst_3432_);
v___x_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3433_, 0, v_fst_3432_);
v___x_3434_ = l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(v___x_3433_, v_maxPrio_x3f_3430_);
lean_dec_ref(v___x_3433_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1___boxed(lean_object* v_maxPrio_x3f_3435_, lean_object* v_x_3436_){
_start:
{
uint8_t v_res_3437_; lean_object* v_r_3438_; 
v_res_3437_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1(v_maxPrio_x3f_3435_, v_x_3436_);
lean_dec_ref(v_x_3436_);
lean_dec(v_maxPrio_x3f_3435_);
v_r_3438_ = lean_box(v_res_3437_);
return v_r_3438_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__2(lean_object* v_a_3439_, lean_object* v_a_3440_){
_start:
{
if (lean_obj_tag(v_a_3439_) == 0)
{
lean_object* v___x_3441_; 
v___x_3441_ = l_List_reverse___redArg(v_a_3440_);
return v___x_3441_;
}
else
{
lean_object* v_head_3442_; lean_object* v_tail_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3452_; 
v_head_3442_ = lean_ctor_get(v_a_3439_, 0);
v_tail_3443_ = lean_ctor_get(v_a_3439_, 1);
v_isSharedCheck_3452_ = !lean_is_exclusive(v_a_3439_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3445_ = v_a_3439_;
v_isShared_3446_ = v_isSharedCheck_3452_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_tail_3443_);
lean_inc(v_head_3442_);
lean_dec(v_a_3439_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3452_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v_fst_3447_; lean_object* v___x_3449_; 
v_fst_3447_ = lean_ctor_get(v_head_3442_, 0);
lean_inc(v_fst_3447_);
lean_dec(v_head_3442_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 1, v_a_3440_);
lean_ctor_set(v___x_3445_, 0, v_fst_3447_);
v___x_3449_ = v___x_3445_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_fst_3447_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_a_3440_);
v___x_3449_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
v_a_3439_ = v_tail_3443_;
v_a_3440_ = v___x_3449_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__0(lean_object* v_filter_3453_, lean_object* v_hoverPos_3454_, uint8_t v_includeStop_3455_, lean_object* v_ctx_3456_, lean_object* v_info_3457_, lean_object* v_children_3458_, lean_object* v_results_3459_){
_start:
{
uint8_t v___y_3461_; uint8_t v___y_3462_; lean_object* v___y_3463_; uint8_t v___y_3464_; uint8_t v___y_3470_; uint8_t v___y_3471_; lean_object* v___y_3472_; uint8_t v___y_3473_; uint8_t v___y_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v_maxPrio_x3f_3480_; lean_object* v___f_3481_; lean_object* v_bestResult_x3f_3482_; 
v___x_3475_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___closed__0));
v___x_3476_ = l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__1(v_results_3459_, v___x_3475_);
lean_inc_ref(v_children_3458_);
lean_inc_ref(v_info_3457_);
lean_inc_ref(v_ctx_3456_);
v___x_3477_ = lean_apply_4(v_filter_3453_, v_ctx_3456_, v_info_3457_, v_children_3458_, v___x_3476_);
v___x_3478_ = lean_box(0);
lean_inc(v___x_3477_);
v___x_3479_ = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__2(v___x_3477_, v___x_3478_);
v_maxPrio_x3f_3480_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(v___x_3479_);
lean_dec(v___x_3479_);
v___f_3481_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3481_, 0, v_maxPrio_x3f_3480_);
v_bestResult_x3f_3482_ = l_List_find_x3f___redArg(v___f_3481_, v___x_3477_);
if (lean_obj_tag(v_bestResult_x3f_3482_) == 1)
{
lean_dec_ref(v_children_3458_);
lean_dec_ref(v_info_3457_);
lean_dec_ref(v_ctx_3456_);
return v_bestResult_x3f_3482_;
}
else
{
lean_object* v___x_3483_; uint8_t v___y_3485_; uint8_t v___y_3486_; uint8_t v___y_3487_; uint8_t v___y_3501_; lean_object* v___x_3505_; uint8_t v___x_3506_; 
lean_dec(v_bestResult_x3f_3482_);
v___x_3483_ = l_Lean_Elab_Info_stx(v_info_3457_);
v___x_3505_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__1));
lean_inc(v___x_3483_);
v___x_3506_ = l_Lean_Syntax_isOfKind(v___x_3483_, v___x_3505_);
if (v___x_3506_ == 0)
{
lean_object* v___x_3507_; 
lean_inc_ref(v_info_3457_);
v___x_3507_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_3457_);
if (lean_obj_tag(v___x_3507_) == 0)
{
v___y_3501_ = v___x_3506_;
goto v___jp_3500_;
}
else
{
lean_object* v_val_3508_; lean_object* v_elaborator_3509_; lean_object* v___x_3510_; uint8_t v___x_3511_; 
v_val_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc(v_val_3508_);
lean_dec_ref(v___x_3507_);
v_elaborator_3509_ = lean_ctor_get(v_val_3508_, 0);
lean_inc(v_elaborator_3509_);
lean_dec(v_val_3508_);
v___x_3510_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6));
v___x_3511_ = lean_name_eq(v_elaborator_3509_, v___x_3510_);
lean_dec(v_elaborator_3509_);
v___y_3501_ = v___x_3511_;
goto v___jp_3500_;
}
}
else
{
v___y_3501_ = v___x_3506_;
goto v___jp_3500_;
}
v___jp_3484_:
{
lean_object* v___x_3488_; 
v___x_3488_ = l_Lean_Syntax_getRange_x3f(v___x_3483_, v___y_3485_);
lean_dec(v___x_3483_);
if (lean_obj_tag(v___x_3488_) == 1)
{
lean_object* v_val_3489_; uint8_t v___x_3490_; 
v_val_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_val_3489_);
lean_dec_ref(v___x_3488_);
v___x_3490_ = l_Lean_Syntax_Range_contains(v_val_3489_, v_hoverPos_3454_, v_includeStop_3455_);
if (v___x_3490_ == 0)
{
lean_object* v___x_3491_; 
lean_dec(v_val_3489_);
lean_dec_ref(v_children_3458_);
lean_dec_ref(v_info_3457_);
lean_dec_ref(v_ctx_3456_);
v___x_3491_ = lean_box(0);
return v___x_3491_;
}
else
{
if (v___y_3487_ == 0)
{
lean_object* v___x_3492_; 
lean_dec(v_val_3489_);
lean_dec_ref(v_children_3458_);
lean_dec_ref(v_info_3457_);
lean_dec_ref(v_ctx_3456_);
v___x_3492_ = lean_box(0);
return v___x_3492_;
}
else
{
lean_object* v_start_3493_; lean_object* v_stop_3494_; uint8_t v___x_3495_; lean_object* v___x_3496_; 
v_start_3493_ = lean_ctor_get(v_val_3489_, 0);
lean_inc(v_start_3493_);
v_stop_3494_ = lean_ctor_get(v_val_3489_, 1);
lean_inc(v_stop_3494_);
lean_dec(v_val_3489_);
v___x_3495_ = lean_nat_dec_eq(v_stop_3494_, v_hoverPos_3454_);
v___x_3496_ = lean_nat_sub(v_stop_3494_, v_start_3493_);
lean_dec(v_start_3493_);
lean_dec(v_stop_3494_);
if (lean_obj_tag(v_info_3457_) == 1)
{
lean_object* v_i_3497_; lean_object* v_expr_3498_; 
v_i_3497_ = lean_ctor_get(v_info_3457_, 0);
v_expr_3498_ = lean_ctor_get(v_i_3497_, 3);
if (lean_obj_tag(v_expr_3498_) == 1)
{
v___y_3470_ = v___y_3485_;
v___y_3471_ = v___x_3495_;
v___y_3472_ = v___x_3496_;
v___y_3473_ = v___y_3486_;
v___y_3474_ = v___y_3485_;
goto v___jp_3469_;
}
else
{
v___y_3470_ = v___y_3485_;
v___y_3471_ = v___x_3495_;
v___y_3472_ = v___x_3496_;
v___y_3473_ = v___y_3486_;
v___y_3474_ = v___y_3486_;
goto v___jp_3469_;
}
}
else
{
v___y_3470_ = v___y_3485_;
v___y_3471_ = v___x_3495_;
v___y_3472_ = v___x_3496_;
v___y_3473_ = v___y_3486_;
v___y_3474_ = v___y_3486_;
goto v___jp_3469_;
}
}
}
}
else
{
lean_object* v___x_3499_; 
lean_dec(v___x_3488_);
lean_dec_ref(v_children_3458_);
lean_dec_ref(v_info_3457_);
lean_dec_ref(v_ctx_3456_);
v___x_3499_ = lean_box(0);
return v___x_3499_;
}
}
v___jp_3500_:
{
if (v___y_3501_ == 0)
{
uint8_t v___x_3502_; 
v___x_3502_ = 1;
switch(lean_obj_tag(v_info_3457_))
{
case 7:
{
v___y_3485_ = v___x_3502_;
v___y_3486_ = v___y_3501_;
v___y_3487_ = v___x_3502_;
goto v___jp_3484_;
}
case 5:
{
v___y_3485_ = v___x_3502_;
v___y_3486_ = v___y_3501_;
v___y_3487_ = v___x_3502_;
goto v___jp_3484_;
}
case 6:
{
v___y_3485_ = v___x_3502_;
v___y_3486_ = v___y_3501_;
v___y_3487_ = v___x_3502_;
goto v___jp_3484_;
}
default: 
{
lean_object* v___x_3503_; 
lean_inc_ref(v_info_3457_);
v___x_3503_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_3457_);
if (lean_obj_tag(v___x_3503_) == 0)
{
v___y_3485_ = v___x_3502_;
v___y_3486_ = v___y_3501_;
v___y_3487_ = v___y_3501_;
goto v___jp_3484_;
}
else
{
lean_dec_ref(v___x_3503_);
v___y_3485_ = v___x_3502_;
v___y_3486_ = v___y_3501_;
v___y_3487_ = v___x_3502_;
goto v___jp_3484_;
}
}
}
}
else
{
lean_object* v___x_3504_; 
lean_dec(v___x_3483_);
lean_dec_ref(v_children_3458_);
lean_dec_ref(v_info_3457_);
lean_dec_ref(v_ctx_3456_);
v___x_3504_ = lean_box(0);
return v___x_3504_;
}
}
}
v___jp_3460_:
{
lean_object* v_priority_3465_; lean_object* v_result_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v_priority_3465_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_priority_3465_, 0, v___y_3463_);
lean_ctor_set_uint8(v_priority_3465_, sizeof(void*)*1, v___y_3462_);
lean_ctor_set_uint8(v_priority_3465_, sizeof(void*)*1 + 1, v___y_3461_);
lean_ctor_set_uint8(v_priority_3465_, sizeof(void*)*1 + 2, v___y_3464_);
v_result_3466_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_result_3466_, 0, v_ctx_3456_);
lean_ctor_set(v_result_3466_, 1, v_info_3457_);
lean_ctor_set(v_result_3466_, 2, v_children_3458_);
v___x_3467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3467_, 0, v_priority_3465_);
lean_ctor_set(v___x_3467_, 1, v_result_3466_);
v___x_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3467_);
return v___x_3468_;
}
v___jp_3469_:
{
if (lean_obj_tag(v_info_3457_) == 2)
{
v___y_3461_ = v___y_3474_;
v___y_3462_ = v___y_3471_;
v___y_3463_ = v___y_3472_;
v___y_3464_ = v___y_3470_;
goto v___jp_3460_;
}
else
{
v___y_3461_ = v___y_3474_;
v___y_3462_ = v___y_3471_;
v___y_3463_ = v___y_3472_;
v___y_3464_ = v___y_3473_;
goto v___jp_3460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__0___boxed(lean_object* v_filter_3512_, lean_object* v_hoverPos_3513_, lean_object* v_includeStop_3514_, lean_object* v_ctx_3515_, lean_object* v_info_3516_, lean_object* v_children_3517_, lean_object* v_results_3518_){
_start:
{
uint8_t v_includeStop_boxed_3519_; lean_object* v_res_3520_; 
v_includeStop_boxed_3519_ = lean_unbox(v_includeStop_3514_);
v_res_3520_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__0(v_filter_3512_, v_hoverPos_3513_, v_includeStop_boxed_3519_, v_ctx_3515_, v_info_3516_, v_children_3517_, v_results_3518_);
lean_dec(v_hoverPos_3513_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(lean_object* v_t_3521_, lean_object* v_hoverPos_3522_, uint8_t v_includeStop_3523_, lean_object* v_filter_3524_){
_start:
{
lean_object* v___f_3525_; lean_object* v___x_3526_; lean_object* v_postNode_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___f_3525_ = ((lean_object*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___closed__0));
v___x_3526_ = lean_box(v_includeStop_3523_);
v_postNode_3527_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__0___boxed), 7, 3);
lean_closure_set(v_postNode_3527_, 0, v_filter_3524_);
lean_closure_set(v_postNode_3527_, 1, v_hoverPos_3522_);
lean_closure_set(v_postNode_3527_, 2, v___x_3526_);
v___x_3528_ = lean_box(0);
v___x_3529_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v___f_3525_, v_postNode_3527_, v___x_3528_, v_t_3521_);
if (lean_obj_tag(v___x_3529_) == 0)
{
return v___x_3528_;
}
else
{
lean_object* v_val_3530_; 
v_val_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_val_3530_);
lean_dec_ref(v___x_3529_);
if (lean_obj_tag(v_val_3530_) == 0)
{
return v___x_3528_;
}
else
{
lean_object* v_val_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3543_; 
v_val_3531_ = lean_ctor_get(v_val_3530_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v_val_3530_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3533_ = v_val_3530_;
v_isShared_3534_ = v_isSharedCheck_3543_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_val_3531_);
lean_dec(v_val_3530_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3543_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v_snd_3535_; lean_object* v_info_3536_; lean_object* v___x_3538_; 
v_snd_3535_ = lean_ctor_get(v_val_3531_, 1);
lean_inc(v_snd_3535_);
lean_dec(v_val_3531_);
v_info_3536_ = lean_ctor_get(v_snd_3535_, 1);
lean_inc_ref(v_info_3536_);
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 0, v_snd_3535_);
v___x_3538_ = v___x_3533_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_snd_3535_);
v___x_3538_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
if (lean_obj_tag(v_info_3536_) == 1)
{
lean_object* v_i_3539_; lean_object* v_expr_3540_; uint8_t v___x_3541_; 
v_i_3539_ = lean_ctor_get(v_info_3536_, 0);
lean_inc_ref(v_i_3539_);
lean_dec_ref(v_info_3536_);
v_expr_3540_ = lean_ctor_get(v_i_3539_, 3);
lean_inc_ref(v_expr_3540_);
lean_dec_ref(v_i_3539_);
v___x_3541_ = l_Lean_Expr_isSyntheticSorry(v_expr_3540_);
lean_dec_ref(v_expr_3540_);
if (v___x_3541_ == 0)
{
return v___x_3538_;
}
else
{
lean_dec_ref(v___x_3538_);
return v___x_3528_;
}
}
else
{
lean_dec_ref(v_info_3536_);
return v___x_3538_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___boxed(lean_object* v_t_3544_, lean_object* v_hoverPos_3545_, lean_object* v_includeStop_3546_, lean_object* v_filter_3547_){
_start:
{
uint8_t v_includeStop_boxed_3548_; lean_object* v_res_3549_; 
v_includeStop_boxed_3548_ = lean_unbox(v_includeStop_3546_);
v_res_3549_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(v_t_3544_, v_hoverPos_3545_, v_includeStop_boxed_3548_, v_filter_3547_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f(lean_object* v_t_3551_, lean_object* v_hoverPos_3552_){
_start:
{
lean_object* v_filter_3553_; uint8_t v___x_3554_; lean_object* v___x_3555_; 
v_filter_3553_ = ((lean_object*)(l_Lean_Elab_InfoTree_termGoalAt_x3f___closed__0));
v___x_3554_ = 1;
v___x_3555_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(v_t_3551_, v_hoverPos_3552_, v___x_3554_, v_filter_3553_);
return v___x_3555_;
}
}
lean_object* runtime_initialize_Lean_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_InfoUtils(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_instLEHoverableInfoPrio = _init_l_Lean_Elab_instLEHoverableInfoPrio();
lean_mark_persistent(l_Lean_Elab_instLEHoverableInfoPrio);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_InfoUtils(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_DocString(uint8_t builtin);
lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_InfoUtils(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_InfoUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_InfoUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_InfoUtils(builtin);
}
#ifdef __cplusplus
}
#endif
