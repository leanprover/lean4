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
lean_object* l_Lean_Elab_Info_toElabInfo_x3f(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_Meta_getPPContext(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecls();
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_OptionDecl_fullDescr(lean_object*);
extern lean_object* l_Lean_errorExplanationExt;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ErrorExplanation_summaryWithSeverity(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
lean_object* l_Lean_Elab_Info_stx(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSyntheticSorry(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTrailingSize(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_List_filterMapTR_go___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_List_mapM_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_max_x3f___redArg(lean_object*, lean_object*);
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1___boxed(lean_object* v_x_23_, lean_object* v_i_24_, lean_object* v_inst_25_, lean_object* v_preNode_26_, lean_object* v_postNode_27_, lean_object* v_children_28_, lean_object* v_toBind_29_, lean_object* v___f_30_, lean_object* v_val_31_, lean_object* v___f_32_, lean_object* v_visitChildren_33_){
_start:
{
uint8_t v_visitChildren_boxed_34_; lean_object* v_res_35_; 
v_visitChildren_boxed_34_ = lean_unbox(v_visitChildren_33_);
v_res_35_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1(v_x_23_, v_i_24_, v_inst_25_, v_preNode_26_, v_postNode_27_, v_children_28_, v_toBind_29_, v___f_30_, v_val_31_, v___f_32_, v_visitChildren_boxed_34_);
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
lean_dec_ref_known(v_x_40_, 2);
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
lean_dec_ref_known(v_x_40_, 2);
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
lean_dec_ref_known(v_x_40_, 2);
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
lean_closure_set(v___f_57_, 0, v_x_39_);
lean_closure_set(v___f_57_, 1, v_i_52_);
lean_closure_set(v___f_57_, 2, v_inst_36_);
lean_closure_set(v___f_57_, 3, v_preNode_37_);
lean_closure_set(v___f_57_, 4, v_postNode_38_);
lean_closure_set(v___f_57_, 5, v_children_53_);
lean_closure_set(v___f_57_, 6, v_toBind_50_);
lean_closure_set(v___f_57_, 7, v___f_56_);
lean_closure_set(v___f_57_, 8, v_val_54_);
lean_closure_set(v___f_57_, 9, v___f_55_);
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
lean_dec_ref_known(v_x_40_, 1);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1(lean_object* v_x_64_, lean_object* v_i_65_, lean_object* v_inst_66_, lean_object* v_preNode_67_, lean_object* v_postNode_68_, lean_object* v_children_69_, lean_object* v_toBind_70_, lean_object* v___f_71_, lean_object* v_val_72_, lean_object* v___f_73_, uint8_t v_visitChildren_74_){
_start:
{
uint8_t v___x_75_; 
v___x_75_ = lean_bool_not(v_visitChildren_74_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec(v___f_73_);
lean_dec_ref(v_val_72_);
v___x_76_ = l_Lean_Elab_Info_updateContext_x3f(v_x_64_, v_i_65_);
lean_dec_ref(v_i_65_);
lean_inc_ref(v_inst_66_);
v___x_77_ = lean_alloc_closure((void*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg), 5, 4);
lean_closure_set(v___x_77_, 0, v_inst_66_);
lean_closure_set(v___x_77_, 1, v_preNode_67_);
lean_closure_set(v___x_77_, 2, v_postNode_68_);
lean_closure_set(v___x_77_, 3, v___x_76_);
v___x_78_ = l_Lean_PersistentArray_toList___redArg(v_children_69_);
lean_dec_ref(v_children_69_);
v___x_79_ = lean_box(0);
v___x_80_ = l_List_mapM_loop___redArg(v_inst_66_, v___x_77_, v___x_78_, v___x_79_);
v___x_81_ = lean_apply_4(v_toBind_70_, lean_box(0), lean_box(0), v___x_80_, v___f_71_);
return v___x_81_;
}
else
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec(v___f_71_);
lean_dec(v_preNode_67_);
lean_dec_ref(v_inst_66_);
lean_dec(v_x_64_);
v___x_82_ = lean_box(0);
v___x_83_ = lean_apply_4(v_postNode_68_, v_val_72_, v_i_65_, v_children_69_, v___x_82_);
v___x_84_ = lean_apply_4(v_toBind_70_, lean_box(0), lean_box(0), v___x_83_, v___f_73_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go(lean_object* v_m_85_, lean_object* v_00_u03b1_86_, lean_object* v_inst_87_, lean_object* v_preNode_88_, lean_object* v_postNode_89_, lean_object* v_x_90_, lean_object* v_x_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_87_, v_preNode_88_, v_postNode_89_, v_x_90_, v_x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM___redArg(lean_object* v_inst_93_, lean_object* v_preNode_94_, lean_object* v_postNode_95_, lean_object* v_ctx_x3f_96_, lean_object* v_x_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_93_, v_preNode_94_, v_postNode_95_, v_ctx_x3f_96_, v_x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM(lean_object* v_m_99_, lean_object* v_00_u03b1_100_, lean_object* v_inst_101_, lean_object* v_preNode_102_, lean_object* v_postNode_103_, lean_object* v_ctx_x3f_104_, lean_object* v_x_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_101_, v_preNode_102_, v_postNode_103_, v_ctx_x3f_104_, v_x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___redArg___lam__0(lean_object* v_postNode_107_, lean_object* v_ci_108_, lean_object* v_i_109_, lean_object* v_cs_110_, lean_object* v_x_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_apply_3(v_postNode_107_, v_ci_108_, v_i_109_, v_cs_110_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___redArg___lam__0___boxed(lean_object* v_postNode_113_, lean_object* v_ci_114_, lean_object* v_i_115_, lean_object* v_cs_116_, lean_object* v_x_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Elab_InfoTree_visitM_x27___redArg___lam__0(v_postNode_113_, v_ci_114_, v_i_115_, v_cs_116_, v_x_117_);
lean_dec(v_x_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___redArg(lean_object* v_inst_119_, lean_object* v_preNode_120_, lean_object* v_postNode_121_, lean_object* v_ctx_x3f_122_, lean_object* v_t_123_){
_start:
{
lean_object* v_toApplicative_124_; lean_object* v_toFunctor_125_; lean_object* v_mapConst_126_; lean_object* v___f_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v_toApplicative_124_ = lean_ctor_get(v_inst_119_, 0);
v_toFunctor_125_ = lean_ctor_get(v_toApplicative_124_, 0);
v_mapConst_126_ = lean_ctor_get(v_toFunctor_125_, 1);
lean_inc(v_mapConst_126_);
v___f_127_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_127_, 0, v_postNode_121_);
v___x_128_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_119_, v_preNode_120_, v___f_127_, v_ctx_x3f_122_, v_t_123_);
v___x_129_ = lean_box(0);
v___x_130_ = lean_apply_4(v_mapConst_126_, lean_box(0), lean_box(0), v___x_129_, v___x_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27(lean_object* v_m_131_, lean_object* v_inst_132_, lean_object* v_preNode_133_, lean_object* v_postNode_134_, lean_object* v_ctx_x3f_135_, lean_object* v_t_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_Elab_InfoTree_visitM_x27___redArg(v_inst_132_, v_preNode_133_, v_postNode_134_, v_ctx_x3f_135_, v_t_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__0(lean_object* v_x_138_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
lean_object* v___x_139_; 
v___x_139_ = lean_box(0);
return v___x_139_;
}
else
{
lean_object* v_val_140_; 
v_val_140_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_val_140_);
return v_val_140_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__0___boxed(lean_object* v_x_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__0(v_x_141_);
lean_dec(v_x_141_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1(lean_object* v_p_146_, lean_object* v_ci_147_, lean_object* v_i_148_, lean_object* v_cs_149_, lean_object* v_as_150_){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_151_ = ((lean_object*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1___closed__0));
v___x_152_ = ((lean_object*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1___closed__1));
v___x_153_ = l_List_filterMapTR_go___redArg(v___x_151_, v_as_150_, v___x_152_);
v___x_154_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_151_, v___x_153_, v___x_152_);
v___x_155_ = lean_apply_4(v_p_146_, v_ci_147_, v_i_148_, v_cs_149_, v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__2(lean_object* v_toPure_156_, lean_object* v_x_157_, lean_object* v_x_158_, lean_object* v_x_159_){
_start:
{
uint8_t v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = 1;
v___x_161_ = lean_box(v___x_160_);
v___x_162_ = lean_apply_2(v_toPure_156_, lean_box(0), v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__2___boxed(lean_object* v_toPure_163_, lean_object* v_x_164_, lean_object* v_x_165_, lean_object* v_x_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__2(v_toPure_163_, v_x_164_, v_x_165_, v_x_166_);
lean_dec_ref(v_x_166_);
lean_dec_ref(v_x_165_);
lean_dec_ref(v_x_164_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg(lean_object* v_inst_169_, lean_object* v_p_170_, lean_object* v_i_171_){
_start:
{
lean_object* v_toApplicative_172_; lean_object* v_toFunctor_173_; lean_object* v_toPure_174_; lean_object* v_map_175_; lean_object* v___f_176_; lean_object* v___f_177_; lean_object* v___f_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v_toApplicative_172_ = lean_ctor_get(v_inst_169_, 0);
v_toFunctor_173_ = lean_ctor_get(v_toApplicative_172_, 0);
v_toPure_174_ = lean_ctor_get(v_toApplicative_172_, 1);
v_map_175_ = lean_ctor_get(v_toFunctor_173_, 0);
lean_inc(v_map_175_);
v___f_176_ = ((lean_object*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___closed__0));
v___f_177_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1), 5, 1);
lean_closure_set(v___f_177_, 0, v_p_170_);
lean_inc(v_toPure_174_);
v___f_178_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__2___boxed), 4, 1);
lean_closure_set(v___f_178_, 0, v_toPure_174_);
v___x_179_ = lean_box(0);
v___x_180_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_169_, v___f_178_, v___f_177_, v___x_179_, v_i_171_);
v___x_181_ = lean_apply_4(v_map_175_, lean_box(0), lean_box(0), v___f_176_, v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM(lean_object* v_m_182_, lean_object* v_00_u03b1_183_, lean_object* v_inst_184_, lean_object* v_p_185_, lean_object* v_i_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg(v_inst_184_, v_p_185_, v_i_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg___lam__0(lean_object* v_p_188_, lean_object* v_x1_189_, lean_object* v_x2_190_, lean_object* v_x3_191_, lean_object* v_x4_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lean_apply_4(v_p_188_, v_x1_189_, v_x2_190_, v_x3_191_, v_x4_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__1___redArg(lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
if (lean_obj_tag(v_a_194_) == 0)
{
lean_object* v___x_196_; 
v___x_196_ = lean_array_to_list(v_a_195_);
return v___x_196_;
}
else
{
lean_object* v_head_197_; lean_object* v_tail_198_; lean_object* v___x_199_; 
v_head_197_ = lean_ctor_get(v_a_194_, 0);
lean_inc(v_head_197_);
v_tail_198_ = lean_ctor_get(v_a_194_, 1);
lean_inc(v_tail_198_);
lean_dec_ref_known(v_a_194_, 2);
v___x_199_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_195_, v_head_197_);
v_a_194_ = v_tail_198_;
v_a_195_ = v___x_199_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__0___redArg(lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
if (lean_obj_tag(v_a_201_) == 0)
{
lean_object* v___x_203_; 
v___x_203_ = lean_array_to_list(v_a_202_);
return v___x_203_;
}
else
{
lean_object* v_head_204_; 
v_head_204_ = lean_ctor_get(v_a_201_, 0);
if (lean_obj_tag(v_head_204_) == 0)
{
lean_object* v_tail_205_; 
v_tail_205_ = lean_ctor_get(v_a_201_, 1);
lean_inc(v_tail_205_);
lean_dec_ref_known(v_a_201_, 2);
v_a_201_ = v_tail_205_;
goto _start;
}
else
{
lean_object* v_tail_207_; lean_object* v_val_208_; lean_object* v___x_209_; 
lean_inc_ref(v_head_204_);
v_tail_207_ = lean_ctor_get(v_a_201_, 1);
lean_inc(v_tail_207_);
lean_dec_ref_known(v_a_201_, 2);
v_val_208_ = lean_ctor_get(v_head_204_, 0);
lean_inc(v_val_208_);
lean_dec_ref_known(v_head_204_, 1);
v___x_209_ = lean_array_push(v_a_202_, v_val_208_);
v_a_201_ = v_tail_207_;
v_a_202_ = v___x_209_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__0(lean_object* v_p_211_, lean_object* v_ci_212_, lean_object* v_i_213_, lean_object* v_cs_214_, lean_object* v_as_215_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_216_ = ((lean_object*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__1___closed__1));
v___x_217_ = l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__0___redArg(v_as_215_, v___x_216_);
v___x_218_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__1___redArg(v___x_217_, v___x_216_);
v___x_219_ = lean_apply_4(v_p_211_, v_ci_212_, v_i_213_, v_cs_214_, v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg(lean_object* v_msg_227_){
_start:
{
lean_object* v___f_228_; lean_object* v___f_229_; lean_object* v___f_230_; lean_object* v___f_231_; lean_object* v___f_232_; lean_object* v___f_233_; lean_object* v___f_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___f_228_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__0));
v___f_229_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__1));
v___f_230_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__2));
v___f_231_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__3));
v___f_232_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__4));
v___f_233_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__5));
v___f_234_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__6));
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v___f_228_);
lean_ctor_set(v___x_235_, 1, v___f_229_);
v___x_236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v___f_230_);
lean_ctor_set(v___x_236_, 2, v___f_231_);
lean_ctor_set(v___x_236_, 3, v___f_232_);
lean_ctor_set(v___x_236_, 4, v___f_233_);
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v___f_234_);
v___x_238_ = lean_box(0);
v___x_239_ = l_instInhabitedOfMonad___redArg(v___x_237_, v___x_238_);
v___x_240_ = lean_panic_fn_borrowed(v___x_239_, v_msg_227_);
lean_dec(v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(lean_object* v_preNode_241_, lean_object* v_postNode_242_, lean_object* v_x_243_, lean_object* v_x_244_){
_start:
{
switch(lean_obj_tag(v_x_244_))
{
case 0:
{
lean_object* v_i_245_; lean_object* v_t_246_; lean_object* v___x_247_; 
v_i_245_ = lean_ctor_get(v_x_244_, 0);
lean_inc_ref(v_i_245_);
v_t_246_ = lean_ctor_get(v_x_244_, 1);
lean_inc_ref(v_t_246_);
lean_dec_ref_known(v_x_244_, 2);
v___x_247_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_245_, v_x_243_);
v_x_243_ = v___x_247_;
v_x_244_ = v_t_246_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_243_) == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec_ref_known(v_x_244_, 2);
lean_dec(v_postNode_242_);
lean_dec_ref(v_preNode_241_);
v___x_249_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3);
v___x_250_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg(v___x_249_);
return v___x_250_;
}
else
{
lean_object* v_i_251_; lean_object* v_children_252_; lean_object* v_val_253_; lean_object* v___x_254_; uint8_t v___x_255_; uint8_t v___x_256_; 
v_i_251_ = lean_ctor_get(v_x_244_, 0);
lean_inc_ref_n(v_i_251_, 2);
v_children_252_ = lean_ctor_get(v_x_244_, 1);
lean_inc_ref_n(v_children_252_, 2);
lean_dec_ref_known(v_x_244_, 2);
v_val_253_ = lean_ctor_get(v_x_243_, 0);
lean_inc_n(v_val_253_, 2);
lean_inc_ref(v_preNode_241_);
v___x_254_ = lean_apply_3(v_preNode_241_, v_val_253_, v_i_251_, v_children_252_);
v___x_255_ = lean_unbox(v___x_254_);
v___x_256_ = lean_bool_not(v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_257_ = l_Lean_Elab_Info_updateContext_x3f(v_x_243_, v_i_251_);
v___x_258_ = l_Lean_PersistentArray_toList___redArg(v_children_252_);
v___x_259_ = lean_box(0);
lean_inc(v_postNode_242_);
v___x_260_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4___redArg(v_preNode_241_, v_postNode_242_, v___x_257_, v___x_258_, v___x_259_);
v___x_261_ = lean_apply_4(v_postNode_242_, v_val_253_, v_i_251_, v_children_252_, v___x_260_);
v___x_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
else
{
lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_271_; 
lean_dec_ref(v_preNode_241_);
v_isSharedCheck_271_ = !lean_is_exclusive(v_x_243_);
if (v_isSharedCheck_271_ == 0)
{
lean_object* v_unused_272_; 
v_unused_272_ = lean_ctor_get(v_x_243_, 0);
lean_dec(v_unused_272_);
v___x_264_ = v_x_243_;
v_isShared_265_ = v_isSharedCheck_271_;
goto v_resetjp_263_;
}
else
{
lean_dec(v_x_243_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_271_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_266_ = lean_box(0);
v___x_267_ = lean_apply_4(v_postNode_242_, v_val_253_, v_i_251_, v_children_252_, v___x_266_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 0, v___x_267_);
v___x_269_ = v___x_264_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
}
default: 
{
lean_object* v___x_273_; 
lean_dec_ref_known(v_x_244_, 1);
lean_dec(v_x_243_);
lean_dec(v_postNode_242_);
lean_dec_ref(v_preNode_241_);
v___x_273_ = lean_box(0);
return v___x_273_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4___redArg(lean_object* v_preNode_274_, lean_object* v_postNode_275_, lean_object* v___x_276_, lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
if (lean_obj_tag(v_x_277_) == 0)
{
lean_object* v___x_279_; 
lean_dec(v___x_276_);
lean_dec(v_postNode_275_);
lean_dec_ref(v_preNode_274_);
v___x_279_ = l_List_reverse___redArg(v_x_278_);
return v___x_279_;
}
else
{
lean_object* v_head_280_; lean_object* v_tail_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_290_; 
v_head_280_ = lean_ctor_get(v_x_277_, 0);
v_tail_281_ = lean_ctor_get(v_x_277_, 1);
v_isSharedCheck_290_ = !lean_is_exclusive(v_x_277_);
if (v_isSharedCheck_290_ == 0)
{
v___x_283_ = v_x_277_;
v_isShared_284_ = v_isSharedCheck_290_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_tail_281_);
lean_inc(v_head_280_);
lean_dec(v_x_277_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_290_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
lean_inc(v___x_276_);
lean_inc(v_postNode_275_);
lean_inc_ref(v_preNode_274_);
v___x_285_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v_preNode_274_, v_postNode_275_, v___x_276_, v_head_280_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v_x_278_);
lean_ctor_set(v___x_283_, 0, v___x_285_);
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_285_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_x_278_);
v___x_287_ = v_reuseFailAlloc_289_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
v_x_277_ = v_tail_281_;
v_x_278_ = v___x_287_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__1(lean_object* v_x_291_, lean_object* v_x_292_, lean_object* v_x_293_){
_start:
{
uint8_t v___x_294_; 
v___x_294_ = 1;
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__1___boxed(lean_object* v_x_295_, lean_object* v_x_296_, lean_object* v_x_297_){
_start:
{
uint8_t v_res_298_; lean_object* v_r_299_; 
v_res_298_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__1(v_x_295_, v_x_296_, v_x_297_);
lean_dec_ref(v_x_297_);
lean_dec_ref(v_x_296_);
lean_dec_ref(v_x_295_);
v_r_299_ = lean_box(v_res_298_);
return v_r_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg(lean_object* v_p_301_, lean_object* v_i_302_){
_start:
{
lean_object* v___f_303_; lean_object* v___f_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___f_303_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__0), 5, 1);
lean_closure_set(v___f_303_, 0, v_p_301_);
v___f_304_ = ((lean_object*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___closed__0));
v___x_305_ = lean_box(0);
v___x_306_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v___f_304_, v___f_303_, v___x_305_, v_i_302_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v___x_307_; 
v___x_307_ = lean_box(0);
return v___x_307_;
}
else
{
lean_object* v_val_308_; 
v_val_308_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_val_308_);
lean_dec_ref_known(v___x_306_, 1);
return v_val_308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg(lean_object* v_p_309_, lean_object* v_i_310_){
_start:
{
lean_object* v___f_311_; lean_object* v___x_312_; 
v___f_311_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg___lam__0), 5, 1);
lean_closure_set(v___f_311_, 0, v_p_309_);
v___x_312_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg(v___f_311_, v_i_310_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUp(lean_object* v_00_u03b1_313_, lean_object* v_p_314_, lean_object* v_i_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg(v_p_314_, v_i_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0(lean_object* v_00_u03b1_317_, lean_object* v_p_318_, lean_object* v_i_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg(v_p_318_, v_i_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__0(lean_object* v_00_u03b1_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__0___redArg(v_a_322_, v_a_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__1(lean_object* v_00_u03b1_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__1___redArg(v_a_326_, v_a_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_329_, lean_object* v_msg_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg(v_msg_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2(lean_object* v_00_u03b1_332_, lean_object* v_preNode_333_, lean_object* v_postNode_334_, lean_object* v_x_335_, lean_object* v_x_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v_preNode_333_, v_postNode_334_, v_x_335_, v_x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_338_, lean_object* v_preNode_339_, lean_object* v_postNode_340_, lean_object* v___x_341_, lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4___redArg(v_preNode_339_, v_postNode_340_, v___x_341_, v_x_342_, v_x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0(lean_object* v_inst_345_, lean_object* v_____do__lift_346_){
_start:
{
if (lean_obj_tag(v_____do__lift_346_) == 0)
{
lean_object* v_toApplicative_347_; lean_object* v_toPure_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_toApplicative_347_ = lean_ctor_get(v_inst_345_, 0);
lean_inc_ref(v_toApplicative_347_);
lean_dec_ref(v_inst_345_);
v_toPure_348_ = lean_ctor_get(v_toApplicative_347_, 1);
lean_inc(v_toPure_348_);
lean_dec_ref(v_toApplicative_347_);
v___x_349_ = lean_box(0);
v___x_350_ = lean_apply_2(v_toPure_348_, lean_box(0), v___x_349_);
return v___x_350_;
}
else
{
lean_object* v_toApplicative_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_362_; 
v_toApplicative_351_ = lean_ctor_get(v_inst_345_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v_inst_345_);
if (v_isSharedCheck_362_ == 0)
{
lean_object* v_unused_363_; 
v_unused_363_ = lean_ctor_get(v_inst_345_, 1);
lean_dec(v_unused_363_);
v___x_353_ = v_inst_345_;
v_isShared_354_ = v_isSharedCheck_362_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_toApplicative_351_);
lean_dec(v_inst_345_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_362_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v_val_355_; lean_object* v_toPure_356_; lean_object* v___x_357_; lean_object* v___x_359_; 
v_val_355_ = lean_ctor_get(v_____do__lift_346_, 0);
v_toPure_356_ = lean_ctor_get(v_toApplicative_351_, 1);
lean_inc(v_toPure_356_);
lean_dec_ref(v_toApplicative_351_);
v___x_357_ = lean_box(0);
lean_inc(v_val_355_);
if (v_isShared_354_ == 0)
{
lean_ctor_set_tag(v___x_353_, 1);
lean_ctor_set(v___x_353_, 1, v___x_357_);
lean_ctor_set(v___x_353_, 0, v_val_355_);
v___x_359_ = v___x_353_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_val_355_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v___x_357_);
v___x_359_ = v_reuseFailAlloc_361_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_360_; 
v___x_360_ = lean_apply_2(v_toPure_356_, lean_box(0), v___x_359_);
return v___x_360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0___boxed(lean_object* v_inst_364_, lean_object* v_____do__lift_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0(v_inst_364_, v_____do__lift_365_);
lean_dec(v_____do__lift_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__1(lean_object* v_inst_367_, lean_object* v_p_368_, lean_object* v___f_369_, lean_object* v_ctx_370_, lean_object* v_i_371_, lean_object* v_cs_372_, lean_object* v_rs_373_){
_start:
{
uint8_t v___x_374_; 
v___x_374_ = l_List_isEmpty___redArg(v_rs_373_);
if (v___x_374_ == 0)
{
lean_object* v_toApplicative_375_; lean_object* v_toPure_376_; lean_object* v___x_377_; 
lean_dec_ref(v_cs_372_);
lean_dec_ref(v_i_371_);
lean_dec_ref(v_ctx_370_);
lean_dec(v___f_369_);
lean_dec(v_p_368_);
v_toApplicative_375_ = lean_ctor_get(v_inst_367_, 0);
lean_inc_ref(v_toApplicative_375_);
lean_dec_ref(v_inst_367_);
v_toPure_376_ = lean_ctor_get(v_toApplicative_375_, 1);
lean_inc(v_toPure_376_);
lean_dec_ref(v_toApplicative_375_);
v___x_377_ = lean_apply_2(v_toPure_376_, lean_box(0), v_rs_373_);
return v___x_377_;
}
else
{
lean_object* v_toBind_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
lean_dec(v_rs_373_);
v_toBind_378_ = lean_ctor_get(v_inst_367_, 1);
lean_inc(v_toBind_378_);
lean_dec_ref(v_inst_367_);
v___x_379_ = lean_apply_3(v_p_368_, v_ctx_370_, v_i_371_, v_cs_372_);
v___x_380_ = lean_apply_4(v_toBind_378_, lean_box(0), lean_box(0), v___x_379_, v___f_369_);
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg(lean_object* v_inst_381_, lean_object* v_p_382_, lean_object* v_infoTree_383_){
_start:
{
lean_object* v___f_384_; lean_object* v___f_385_; lean_object* v___x_386_; 
lean_inc_ref_n(v_inst_381_, 2);
v___f_384_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_384_, 0, v_inst_381_);
v___f_385_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__1), 7, 3);
lean_closure_set(v___f_385_, 0, v_inst_381_);
lean_closure_set(v___f_385_, 1, v_p_382_);
lean_closure_set(v___f_385_, 2, v___f_384_);
v___x_386_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg(v_inst_381_, v___f_385_, v_infoTree_383_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM(lean_object* v_m_387_, lean_object* v_00_u03b1_388_, lean_object* v_inst_389_, lean_object* v_p_390_, lean_object* v_infoTree_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Elab_InfoTree_deepestNodesM___redArg(v_inst_389_, v_p_390_, v_infoTree_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodes___redArg___lam__0(lean_object* v_p_393_, lean_object* v_x1_394_, lean_object* v_x2_395_, lean_object* v_x3_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = lean_apply_3(v_p_393_, v_x1_394_, v_x2_395_, v_x3_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0(lean_object* v_p_398_, lean_object* v_ctx_399_, lean_object* v_i_400_, lean_object* v_cs_401_, lean_object* v_rs_402_){
_start:
{
uint8_t v___x_403_; 
v___x_403_ = l_List_isEmpty___redArg(v_rs_402_);
if (v___x_403_ == 0)
{
lean_dec_ref(v_cs_401_);
lean_dec_ref(v_i_400_);
lean_dec_ref(v_ctx_399_);
lean_dec_ref(v_p_398_);
lean_inc(v_rs_402_);
return v_rs_402_;
}
else
{
lean_object* v___x_404_; 
v___x_404_ = lean_apply_3(v_p_398_, v_ctx_399_, v_i_400_, v_cs_401_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v___x_405_; 
v___x_405_ = lean_box(0);
return v___x_405_;
}
else
{
lean_object* v_val_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v_val_406_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_val_406_);
lean_dec_ref_known(v___x_404_, 1);
v___x_407_ = lean_box(0);
v___x_408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_408_, 0, v_val_406_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0___boxed(lean_object* v_p_409_, lean_object* v_ctx_410_, lean_object* v_i_411_, lean_object* v_cs_412_, lean_object* v_rs_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0(v_p_409_, v_ctx_410_, v_i_411_, v_cs_412_, v_rs_413_);
lean_dec(v_rs_413_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg(lean_object* v_p_415_, lean_object* v_infoTree_416_){
_start:
{
lean_object* v___f_417_; lean_object* v___x_418_; 
v___f_417_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_417_, 0, v_p_415_);
v___x_418_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg(v___f_417_, v_infoTree_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodes___redArg(lean_object* v_p_419_, lean_object* v_infoTree_420_){
_start:
{
lean_object* v___f_421_; lean_object* v___x_422_; 
v___f_421_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_deepestNodes___redArg___lam__0), 4, 1);
lean_closure_set(v___f_421_, 0, v_p_419_);
v___x_422_ = l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg(v___f_421_, v_infoTree_420_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodes(lean_object* v_00_u03b1_423_, lean_object* v_p_424_, lean_object* v_infoTree_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v_p_424_, v_infoTree_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0(lean_object* v_00_u03b1_427_, lean_object* v_p_428_, lean_object* v_infoTree_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg(v_p_428_, v_infoTree_429_);
return v___x_430_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(lean_object* v_f_432_, lean_object* v___x_433_, lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
if (lean_obj_tag(v_x_434_) == 0)
{
lean_object* v_cs_436_; lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v_cs_436_ = lean_ctor_get(v_x_434_, 0);
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = lean_array_get_size(v_cs_436_);
v___x_439_ = lean_nat_dec_lt(v___x_437_, v___x_438_);
if (v___x_439_ == 0)
{
lean_dec(v___x_433_);
lean_dec(v_f_432_);
return v_x_435_;
}
else
{
uint8_t v___x_440_; 
v___x_440_ = lean_nat_dec_le(v___x_438_, v___x_438_);
if (v___x_440_ == 0)
{
if (v___x_439_ == 0)
{
lean_dec(v___x_433_);
lean_dec(v_f_432_);
return v_x_435_;
}
else
{
size_t v___x_441_; size_t v___x_442_; lean_object* v___x_443_; 
v___x_441_ = ((size_t)0ULL);
v___x_442_ = lean_usize_of_nat(v___x_438_);
v___x_443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_432_, v___x_433_, v_cs_436_, v___x_441_, v___x_442_, v_x_435_);
return v___x_443_;
}
}
else
{
size_t v___x_444_; size_t v___x_445_; lean_object* v___x_446_; 
v___x_444_ = ((size_t)0ULL);
v___x_445_ = lean_usize_of_nat(v___x_438_);
v___x_446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_432_, v___x_433_, v_cs_436_, v___x_444_, v___x_445_, v_x_435_);
return v___x_446_;
}
}
}
else
{
lean_object* v_vs_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v_vs_447_ = lean_ctor_get(v_x_434_, 0);
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_array_get_size(v_vs_447_);
v___x_450_ = lean_nat_dec_lt(v___x_448_, v___x_449_);
if (v___x_450_ == 0)
{
lean_dec(v___x_433_);
lean_dec(v_f_432_);
return v_x_435_;
}
else
{
uint8_t v___x_451_; 
v___x_451_ = lean_nat_dec_le(v___x_449_, v___x_449_);
if (v___x_451_ == 0)
{
if (v___x_450_ == 0)
{
lean_dec(v___x_433_);
lean_dec(v_f_432_);
return v_x_435_;
}
else
{
size_t v___x_452_; size_t v___x_453_; lean_object* v___x_454_; 
v___x_452_ = ((size_t)0ULL);
v___x_453_ = lean_usize_of_nat(v___x_449_);
v___x_454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_432_, v___x_433_, v_vs_447_, v___x_452_, v___x_453_, v_x_435_);
return v___x_454_;
}
}
else
{
size_t v___x_455_; size_t v___x_456_; lean_object* v___x_457_; 
v___x_455_ = ((size_t)0ULL);
v___x_456_ = lean_usize_of_nat(v___x_449_);
v___x_457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_432_, v___x_433_, v_vs_447_, v___x_455_, v___x_456_, v_x_435_);
return v___x_457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(lean_object* v_f_458_, lean_object* v___x_459_, lean_object* v_as_460_, size_t v_i_461_, size_t v_stop_462_, lean_object* v_b_463_){
_start:
{
uint8_t v___x_464_; 
v___x_464_ = lean_usize_dec_eq(v_i_461_, v_stop_462_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; size_t v___x_467_; size_t v___x_468_; 
v___x_465_ = lean_array_uget_borrowed(v_as_460_, v_i_461_);
lean_inc(v___x_459_);
lean_inc(v_f_458_);
v___x_466_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(v_f_458_, v___x_459_, v___x_465_, v_b_463_);
v___x_467_ = ((size_t)1ULL);
v___x_468_ = lean_usize_add(v_i_461_, v___x_467_);
v_i_461_ = v___x_468_;
v_b_463_ = v___x_466_;
goto _start;
}
else
{
lean_dec(v___x_459_);
lean_dec(v_f_458_);
return v_b_463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(lean_object* v_f_470_, lean_object* v___x_471_, lean_object* v_x_472_, size_t v_x_473_, size_t v_x_474_, lean_object* v_x_475_){
_start:
{
if (lean_obj_tag(v_x_472_) == 0)
{
lean_object* v_cs_476_; lean_object* v___x_477_; size_t v___x_478_; lean_object* v_j_479_; lean_object* v___x_480_; size_t v___x_481_; size_t v___x_482_; size_t v___x_483_; size_t v___x_484_; size_t v___x_485_; size_t v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v_cs_476_ = lean_ctor_get(v_x_472_, 0);
v___x_477_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0);
v___x_478_ = lean_usize_shift_right(v_x_473_, v_x_474_);
v_j_479_ = lean_usize_to_nat(v___x_478_);
v___x_480_ = lean_array_get_borrowed(v___x_477_, v_cs_476_, v_j_479_);
v___x_481_ = ((size_t)1ULL);
v___x_482_ = lean_usize_shift_left(v___x_481_, v_x_474_);
v___x_483_ = lean_usize_sub(v___x_482_, v___x_481_);
v___x_484_ = lean_usize_land(v_x_473_, v___x_483_);
v___x_485_ = ((size_t)5ULL);
v___x_486_ = lean_usize_sub(v_x_474_, v___x_485_);
lean_inc(v___x_471_);
lean_inc(v_f_470_);
v___x_487_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(v_f_470_, v___x_471_, v___x_480_, v___x_484_, v___x_486_, v_x_475_);
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = lean_nat_add(v_j_479_, v___x_488_);
lean_dec(v_j_479_);
v___x_490_ = lean_array_get_size(v_cs_476_);
v___x_491_ = lean_nat_dec_lt(v___x_489_, v___x_490_);
if (v___x_491_ == 0)
{
lean_dec(v___x_489_);
lean_dec(v___x_471_);
lean_dec(v_f_470_);
return v___x_487_;
}
else
{
uint8_t v___x_492_; 
v___x_492_ = lean_nat_dec_le(v___x_490_, v___x_490_);
if (v___x_492_ == 0)
{
if (v___x_491_ == 0)
{
lean_dec(v___x_489_);
lean_dec(v___x_471_);
lean_dec(v_f_470_);
return v___x_487_;
}
else
{
size_t v___x_493_; size_t v___x_494_; lean_object* v___x_495_; 
v___x_493_ = lean_usize_of_nat(v___x_489_);
lean_dec(v___x_489_);
v___x_494_ = lean_usize_of_nat(v___x_490_);
v___x_495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_470_, v___x_471_, v_cs_476_, v___x_493_, v___x_494_, v___x_487_);
return v___x_495_;
}
}
else
{
size_t v___x_496_; size_t v___x_497_; lean_object* v___x_498_; 
v___x_496_ = lean_usize_of_nat(v___x_489_);
lean_dec(v___x_489_);
v___x_497_ = lean_usize_of_nat(v___x_490_);
v___x_498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_470_, v___x_471_, v_cs_476_, v___x_496_, v___x_497_, v___x_487_);
return v___x_498_;
}
}
}
else
{
lean_object* v_vs_499_; lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v_vs_499_ = lean_ctor_get(v_x_472_, 0);
v___x_500_ = lean_usize_to_nat(v_x_473_);
v___x_501_ = lean_array_get_size(v_vs_499_);
v___x_502_ = lean_nat_dec_lt(v___x_500_, v___x_501_);
if (v___x_502_ == 0)
{
lean_dec(v___x_500_);
lean_dec(v___x_471_);
lean_dec(v_f_470_);
return v_x_475_;
}
else
{
uint8_t v___x_503_; 
v___x_503_ = lean_nat_dec_le(v___x_501_, v___x_501_);
if (v___x_503_ == 0)
{
if (v___x_502_ == 0)
{
lean_dec(v___x_500_);
lean_dec(v___x_471_);
lean_dec(v_f_470_);
return v_x_475_;
}
else
{
size_t v___x_504_; size_t v___x_505_; lean_object* v___x_506_; 
v___x_504_ = lean_usize_of_nat(v___x_500_);
lean_dec(v___x_500_);
v___x_505_ = lean_usize_of_nat(v___x_501_);
v___x_506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_470_, v___x_471_, v_vs_499_, v___x_504_, v___x_505_, v_x_475_);
return v___x_506_;
}
}
else
{
size_t v___x_507_; size_t v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_usize_of_nat(v___x_500_);
lean_dec(v___x_500_);
v___x_508_ = lean_usize_of_nat(v___x_501_);
v___x_509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_470_, v___x_471_, v_vs_499_, v___x_507_, v___x_508_, v_x_475_);
return v___x_509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(lean_object* v_f_510_, lean_object* v___x_511_, lean_object* v_t_512_, lean_object* v_init_513_, lean_object* v_start_514_){
_start:
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_unsigned_to_nat(0u);
v___x_516_ = lean_nat_dec_eq(v_start_514_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v_root_517_; lean_object* v_tail_518_; size_t v_shift_519_; lean_object* v_tailOff_520_; uint8_t v___x_521_; 
v_root_517_ = lean_ctor_get(v_t_512_, 0);
v_tail_518_ = lean_ctor_get(v_t_512_, 1);
v_shift_519_ = lean_ctor_get_usize(v_t_512_, 4);
v_tailOff_520_ = lean_ctor_get(v_t_512_, 3);
v___x_521_ = lean_nat_dec_le(v_tailOff_520_, v_start_514_);
if (v___x_521_ == 0)
{
size_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_522_ = lean_usize_of_nat(v_start_514_);
lean_inc(v___x_511_);
lean_inc(v_f_510_);
v___x_523_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(v_f_510_, v___x_511_, v_root_517_, v___x_522_, v_shift_519_, v_init_513_);
v___x_524_ = lean_array_get_size(v_tail_518_);
v___x_525_ = lean_nat_dec_lt(v___x_515_, v___x_524_);
if (v___x_525_ == 0)
{
lean_dec(v___x_511_);
lean_dec(v_f_510_);
return v___x_523_;
}
else
{
uint8_t v___x_526_; 
v___x_526_ = lean_nat_dec_le(v___x_524_, v___x_524_);
if (v___x_526_ == 0)
{
if (v___x_525_ == 0)
{
lean_dec(v___x_511_);
lean_dec(v_f_510_);
return v___x_523_;
}
else
{
size_t v___x_527_; size_t v___x_528_; lean_object* v___x_529_; 
v___x_527_ = ((size_t)0ULL);
v___x_528_ = lean_usize_of_nat(v___x_524_);
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_510_, v___x_511_, v_tail_518_, v___x_527_, v___x_528_, v___x_523_);
return v___x_529_;
}
}
else
{
size_t v___x_530_; size_t v___x_531_; lean_object* v___x_532_; 
v___x_530_ = ((size_t)0ULL);
v___x_531_ = lean_usize_of_nat(v___x_524_);
v___x_532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_510_, v___x_511_, v_tail_518_, v___x_530_, v___x_531_, v___x_523_);
return v___x_532_;
}
}
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_533_ = lean_nat_sub(v_start_514_, v_tailOff_520_);
v___x_534_ = lean_array_get_size(v_tail_518_);
v___x_535_ = lean_nat_dec_lt(v___x_533_, v___x_534_);
if (v___x_535_ == 0)
{
lean_dec(v___x_533_);
lean_dec(v___x_511_);
lean_dec(v_f_510_);
return v_init_513_;
}
else
{
uint8_t v___x_536_; 
v___x_536_ = lean_nat_dec_le(v___x_534_, v___x_534_);
if (v___x_536_ == 0)
{
if (v___x_535_ == 0)
{
lean_dec(v___x_533_);
lean_dec(v___x_511_);
lean_dec(v_f_510_);
return v_init_513_;
}
else
{
size_t v___x_537_; size_t v___x_538_; lean_object* v___x_539_; 
v___x_537_ = lean_usize_of_nat(v___x_533_);
lean_dec(v___x_533_);
v___x_538_ = lean_usize_of_nat(v___x_534_);
v___x_539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_510_, v___x_511_, v_tail_518_, v___x_537_, v___x_538_, v_init_513_);
return v___x_539_;
}
}
else
{
size_t v___x_540_; size_t v___x_541_; lean_object* v___x_542_; 
v___x_540_ = lean_usize_of_nat(v___x_533_);
lean_dec(v___x_533_);
v___x_541_ = lean_usize_of_nat(v___x_534_);
v___x_542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_510_, v___x_511_, v_tail_518_, v___x_540_, v___x_541_, v_init_513_);
return v___x_542_;
}
}
}
}
else
{
lean_object* v_root_543_; lean_object* v_tail_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v_root_543_ = lean_ctor_get(v_t_512_, 0);
v_tail_544_ = lean_ctor_get(v_t_512_, 1);
lean_inc(v___x_511_);
lean_inc(v_f_510_);
v___x_545_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(v_f_510_, v___x_511_, v_root_543_, v_init_513_);
v___x_546_ = lean_array_get_size(v_tail_544_);
v___x_547_ = lean_nat_dec_lt(v___x_515_, v___x_546_);
if (v___x_547_ == 0)
{
lean_dec(v___x_511_);
lean_dec(v_f_510_);
return v___x_545_;
}
else
{
uint8_t v___x_548_; 
v___x_548_ = lean_nat_dec_le(v___x_546_, v___x_546_);
if (v___x_548_ == 0)
{
if (v___x_547_ == 0)
{
lean_dec(v___x_511_);
lean_dec(v_f_510_);
return v___x_545_;
}
else
{
size_t v___x_549_; size_t v___x_550_; lean_object* v___x_551_; 
v___x_549_ = ((size_t)0ULL);
v___x_550_ = lean_usize_of_nat(v___x_546_);
v___x_551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_510_, v___x_511_, v_tail_544_, v___x_549_, v___x_550_, v___x_545_);
return v___x_551_;
}
}
else
{
size_t v___x_552_; size_t v___x_553_; lean_object* v___x_554_; 
v___x_552_ = ((size_t)0ULL);
v___x_553_ = lean_usize_of_nat(v___x_546_);
v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_510_, v___x_511_, v_tail_544_, v___x_552_, v___x_553_, v___x_545_);
return v___x_554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go___redArg(lean_object* v_f_555_, lean_object* v_ctx_x3f_556_, lean_object* v_a_557_, lean_object* v_x_558_){
_start:
{
switch(lean_obj_tag(v_x_558_))
{
case 0:
{
lean_object* v_i_559_; lean_object* v_t_560_; lean_object* v___x_561_; 
v_i_559_ = lean_ctor_get(v_x_558_, 0);
lean_inc_ref(v_i_559_);
v_t_560_ = lean_ctor_get(v_x_558_, 1);
lean_inc_ref(v_t_560_);
lean_dec_ref_known(v_x_558_, 2);
v___x_561_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_559_, v_ctx_x3f_556_);
v_ctx_x3f_556_ = v___x_561_;
v_x_558_ = v_t_560_;
goto _start;
}
case 1:
{
lean_object* v_i_563_; lean_object* v_children_564_; lean_object* v___y_566_; 
v_i_563_ = lean_ctor_get(v_x_558_, 0);
lean_inc_ref(v_i_563_);
v_children_564_ = lean_ctor_get(v_x_558_, 1);
lean_inc_ref(v_children_564_);
lean_dec_ref_known(v_x_558_, 2);
if (lean_obj_tag(v_ctx_x3f_556_) == 0)
{
v___y_566_ = v_a_557_;
goto v___jp_565_;
}
else
{
lean_object* v_val_570_; lean_object* v___x_571_; 
v_val_570_ = lean_ctor_get(v_ctx_x3f_556_, 0);
lean_inc(v_f_555_);
lean_inc_ref(v_i_563_);
lean_inc(v_val_570_);
v___x_571_ = lean_apply_3(v_f_555_, v_val_570_, v_i_563_, v_a_557_);
v___y_566_ = v___x_571_;
goto v___jp_565_;
}
v___jp_565_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_556_, v_i_563_);
lean_dec_ref(v_i_563_);
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(v_f_555_, v___x_567_, v_children_564_, v___y_566_, v___x_568_);
lean_dec_ref(v_children_564_);
return v___x_569_;
}
}
default: 
{
lean_dec_ref_known(v_x_558_, 1);
lean_dec(v_ctx_x3f_556_);
lean_dec(v_f_555_);
return v_a_557_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(lean_object* v_f_572_, lean_object* v___x_573_, lean_object* v_as_574_, size_t v_i_575_, size_t v_stop_576_, lean_object* v_b_577_){
_start:
{
uint8_t v___x_578_; 
v___x_578_ = lean_usize_dec_eq(v_i_575_, v_stop_576_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; size_t v___x_581_; size_t v___x_582_; 
v___x_579_ = lean_array_uget_borrowed(v_as_574_, v_i_575_);
lean_inc(v___x_579_);
lean_inc(v___x_573_);
lean_inc(v_f_572_);
v___x_580_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go___redArg(v_f_572_, v___x_573_, v_b_577_, v___x_579_);
v___x_581_ = ((size_t)1ULL);
v___x_582_ = lean_usize_add(v_i_575_, v___x_581_);
v_i_575_ = v___x_582_;
v_b_577_ = v___x_580_;
goto _start;
}
else
{
lean_dec(v___x_573_);
lean_dec(v_f_572_);
return v_b_577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg___boxed(lean_object* v_f_584_, lean_object* v___x_585_, lean_object* v_as_586_, lean_object* v_i_587_, lean_object* v_stop_588_, lean_object* v_b_589_){
_start:
{
size_t v_i_boxed_590_; size_t v_stop_boxed_591_; lean_object* v_res_592_; 
v_i_boxed_590_ = lean_unbox_usize(v_i_587_);
lean_dec(v_i_587_);
v_stop_boxed_591_ = lean_unbox_usize(v_stop_588_);
lean_dec(v_stop_588_);
v_res_592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_584_, v___x_585_, v_as_586_, v_i_boxed_590_, v_stop_boxed_591_, v_b_589_);
lean_dec_ref(v_as_586_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_593_, lean_object* v___x_594_, lean_object* v_as_595_, lean_object* v_i_596_, lean_object* v_stop_597_, lean_object* v_b_598_){
_start:
{
size_t v_i_boxed_599_; size_t v_stop_boxed_600_; lean_object* v_res_601_; 
v_i_boxed_599_ = lean_unbox_usize(v_i_596_);
lean_dec(v_i_596_);
v_stop_boxed_600_ = lean_unbox_usize(v_stop_597_);
lean_dec(v_stop_597_);
v_res_601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_593_, v___x_594_, v_as_595_, v_i_boxed_599_, v_stop_boxed_600_, v_b_598_);
lean_dec_ref(v_as_595_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg___boxed(lean_object* v_f_602_, lean_object* v___x_603_, lean_object* v_x_604_, lean_object* v_x_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(v_f_602_, v___x_603_, v_x_604_, v_x_605_);
lean_dec_ref(v_x_604_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___boxed(lean_object* v_f_607_, lean_object* v___x_608_, lean_object* v_x_609_, lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
size_t v_x_1543__boxed_613_; size_t v_x_1544__boxed_614_; lean_object* v_res_615_; 
v_x_1543__boxed_613_ = lean_unbox_usize(v_x_610_);
lean_dec(v_x_610_);
v_x_1544__boxed_614_ = lean_unbox_usize(v_x_611_);
lean_dec(v_x_611_);
v_res_615_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(v_f_607_, v___x_608_, v_x_609_, v_x_1543__boxed_613_, v_x_1544__boxed_614_, v_x_612_);
lean_dec_ref(v_x_609_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg___boxed(lean_object* v_f_616_, lean_object* v___x_617_, lean_object* v_t_618_, lean_object* v_init_619_, lean_object* v_start_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(v_f_616_, v___x_617_, v_t_618_, v_init_619_, v_start_620_);
lean_dec(v_start_620_);
lean_dec_ref(v_t_618_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go(lean_object* v_00_u03b1_622_, lean_object* v_f_623_, lean_object* v_ctx_x3f_624_, lean_object* v_a_625_, lean_object* v_x_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go___redArg(v_f_623_, v_ctx_x3f_624_, v_a_625_, v_x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0(lean_object* v_00_u03b1_628_, lean_object* v_f_629_, lean_object* v___x_630_, lean_object* v_t_631_, lean_object* v_init_632_, lean_object* v_start_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(v_f_629_, v___x_630_, v_t_631_, v_init_632_, v_start_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___boxed(lean_object* v_00_u03b1_635_, lean_object* v_f_636_, lean_object* v___x_637_, lean_object* v_t_638_, lean_object* v_init_639_, lean_object* v_start_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0(v_00_u03b1_635_, v_f_636_, v___x_637_, v_t_638_, v_init_639_, v_start_640_);
lean_dec(v_start_640_);
lean_dec_ref(v_t_638_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0(lean_object* v_00_u03b1_642_, lean_object* v_f_643_, lean_object* v___x_644_, lean_object* v_x_645_, size_t v_x_646_, size_t v_x_647_, lean_object* v_x_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(v_f_643_, v___x_644_, v_x_645_, v_x_646_, v_x_647_, v_x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_650_, lean_object* v_f_651_, lean_object* v___x_652_, lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
size_t v_x_1763__boxed_657_; size_t v_x_1764__boxed_658_; lean_object* v_res_659_; 
v_x_1763__boxed_657_ = lean_unbox_usize(v_x_654_);
lean_dec(v_x_654_);
v_x_1764__boxed_658_ = lean_unbox_usize(v_x_655_);
lean_dec(v_x_655_);
v_res_659_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0(v_00_u03b1_650_, v_f_651_, v___x_652_, v_x_653_, v_x_1763__boxed_657_, v_x_1764__boxed_658_, v_x_656_);
lean_dec_ref(v_x_653_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1(lean_object* v_00_u03b1_660_, lean_object* v_f_661_, lean_object* v___x_662_, lean_object* v_as_663_, size_t v_i_664_, size_t v_stop_665_, lean_object* v_b_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_661_, v___x_662_, v_as_663_, v_i_664_, v_stop_665_, v_b_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___boxed(lean_object* v_00_u03b1_668_, lean_object* v_f_669_, lean_object* v___x_670_, lean_object* v_as_671_, lean_object* v_i_672_, lean_object* v_stop_673_, lean_object* v_b_674_){
_start:
{
size_t v_i_boxed_675_; size_t v_stop_boxed_676_; lean_object* v_res_677_; 
v_i_boxed_675_ = lean_unbox_usize(v_i_672_);
lean_dec(v_i_672_);
v_stop_boxed_676_ = lean_unbox_usize(v_stop_673_);
lean_dec(v_stop_673_);
v_res_677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1(v_00_u03b1_668_, v_f_669_, v___x_670_, v_as_671_, v_i_boxed_675_, v_stop_boxed_676_, v_b_674_);
lean_dec_ref(v_as_671_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2(lean_object* v_00_u03b1_678_, lean_object* v_f_679_, lean_object* v___x_680_, lean_object* v_x_681_, lean_object* v_x_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(v_f_679_, v___x_680_, v_x_681_, v_x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___boxed(lean_object* v_00_u03b1_684_, lean_object* v_f_685_, lean_object* v___x_686_, lean_object* v_x_687_, lean_object* v_x_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2(v_00_u03b1_684_, v_f_685_, v___x_686_, v_x_687_, v_x_688_);
lean_dec_ref(v_x_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_690_, lean_object* v_f_691_, lean_object* v___x_692_, lean_object* v_as_693_, size_t v_i_694_, size_t v_stop_695_, lean_object* v_b_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_691_, v___x_692_, v_as_693_, v_i_694_, v_stop_695_, v_b_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_698_, lean_object* v_f_699_, lean_object* v___x_700_, lean_object* v_as_701_, lean_object* v_i_702_, lean_object* v_stop_703_, lean_object* v_b_704_){
_start:
{
size_t v_i_boxed_705_; size_t v_stop_boxed_706_; lean_object* v_res_707_; 
v_i_boxed_705_ = lean_unbox_usize(v_i_702_);
lean_dec(v_i_702_);
v_stop_boxed_706_ = lean_unbox_usize(v_stop_703_);
lean_dec(v_stop_703_);
v_res_707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1(v_00_u03b1_698_, v_f_699_, v___x_700_, v_as_701_, v_i_boxed_705_, v_stop_boxed_706_, v_b_704_);
lean_dec_ref(v_as_701_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfo___redArg(lean_object* v_f_708_, lean_object* v_init_709_, lean_object* v_x_710_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_box(0);
v___x_712_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go___redArg(v_f_708_, v___x_711_, v_init_709_, v_x_710_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfo(lean_object* v_00_u03b1_713_, lean_object* v_f_714_, lean_object* v_init_715_, lean_object* v_x_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v_f_714_, v_init_715_, v_x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__1(lean_object* v___f_718_, lean_object* v_a_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = lean_apply_1(v___f_718_, v_a_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0___boxed(lean_object* v_ctx_x3f_721_, lean_object* v_i_722_, lean_object* v_inst_723_, lean_object* v_f_724_, lean_object* v_children_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0(v_ctx_x3f_721_, v_i_722_, v_inst_723_, v_f_724_, v_children_725_, v_a_726_);
lean_dec_ref(v_i_722_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg(lean_object* v_inst_728_, lean_object* v_f_729_, lean_object* v_ctx_x3f_730_, lean_object* v_a_731_, lean_object* v_x_732_){
_start:
{
switch(lean_obj_tag(v_x_732_))
{
case 0:
{
lean_object* v_i_733_; lean_object* v_t_734_; lean_object* v___x_735_; 
v_i_733_ = lean_ctor_get(v_x_732_, 0);
lean_inc_ref(v_i_733_);
v_t_734_ = lean_ctor_get(v_x_732_, 1);
lean_inc_ref(v_t_734_);
lean_dec_ref_known(v_x_732_, 2);
v___x_735_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_733_, v_ctx_x3f_730_);
v_ctx_x3f_730_ = v___x_735_;
v_x_732_ = v_t_734_;
goto _start;
}
case 1:
{
lean_object* v_toApplicative_737_; lean_object* v_toBind_738_; lean_object* v_toPure_739_; lean_object* v_i_740_; lean_object* v_children_741_; lean_object* v___f_742_; 
v_toApplicative_737_ = lean_ctor_get(v_inst_728_, 0);
v_toBind_738_ = lean_ctor_get(v_inst_728_, 1);
lean_inc(v_toBind_738_);
v_toPure_739_ = lean_ctor_get(v_toApplicative_737_, 1);
lean_inc(v_toPure_739_);
v_i_740_ = lean_ctor_get(v_x_732_, 0);
lean_inc_ref_n(v_i_740_, 2);
v_children_741_ = lean_ctor_get(v_x_732_, 1);
lean_inc_ref(v_children_741_);
lean_dec_ref_known(v_x_732_, 2);
lean_inc(v_f_729_);
lean_inc(v_ctx_x3f_730_);
v___f_742_ = lean_alloc_closure((void*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_742_, 0, v_ctx_x3f_730_);
lean_closure_set(v___f_742_, 1, v_i_740_);
lean_closure_set(v___f_742_, 2, v_inst_728_);
lean_closure_set(v___f_742_, 3, v_f_729_);
lean_closure_set(v___f_742_, 4, v_children_741_);
if (lean_obj_tag(v_ctx_x3f_730_) == 0)
{
lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
lean_dec_ref(v_i_740_);
lean_dec(v_f_729_);
v___f_743_ = lean_alloc_closure((void*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__1), 2, 1);
lean_closure_set(v___f_743_, 0, v___f_742_);
v___x_744_ = lean_apply_2(v_toPure_739_, lean_box(0), v_a_731_);
v___x_745_ = lean_apply_4(v_toBind_738_, lean_box(0), lean_box(0), v___x_744_, v___f_743_);
return v___x_745_;
}
else
{
lean_object* v_val_746_; lean_object* v___f_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
lean_dec(v_toPure_739_);
v_val_746_ = lean_ctor_get(v_ctx_x3f_730_, 0);
lean_inc(v_val_746_);
lean_dec_ref_known(v_ctx_x3f_730_, 1);
v___f_747_ = lean_alloc_closure((void*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__1), 2, 1);
lean_closure_set(v___f_747_, 0, v___f_742_);
v___x_748_ = lean_apply_3(v_f_729_, v_val_746_, v_i_740_, v_a_731_);
v___x_749_ = lean_apply_4(v_toBind_738_, lean_box(0), lean_box(0), v___x_748_, v___f_747_);
return v___x_749_;
}
}
default: 
{
lean_object* v_toApplicative_750_; lean_object* v_toPure_751_; lean_object* v___x_752_; 
v_toApplicative_750_ = lean_ctor_get(v_inst_728_, 0);
lean_inc_ref(v_toApplicative_750_);
lean_dec_ref_known(v_x_732_, 1);
lean_dec(v_ctx_x3f_730_);
lean_dec(v_f_729_);
lean_dec_ref(v_inst_728_);
v_toPure_751_ = lean_ctor_get(v_toApplicative_750_, 1);
lean_inc(v_toPure_751_);
lean_dec_ref(v_toApplicative_750_);
v___x_752_ = lean_apply_2(v_toPure_751_, lean_box(0), v_a_731_);
return v___x_752_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0(lean_object* v_ctx_x3f_753_, lean_object* v_i_754_, lean_object* v_inst_755_, lean_object* v_f_756_, lean_object* v_children_757_, lean_object* v_a_758_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_759_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_753_, v_i_754_);
lean_inc_ref(v_inst_755_);
v___x_760_ = lean_alloc_closure((void*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg), 5, 3);
lean_closure_set(v___x_760_, 0, v_inst_755_);
lean_closure_set(v___x_760_, 1, v_f_756_);
lean_closure_set(v___x_760_, 2, v___x_759_);
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_755_, v_children_757_, v___x_760_, v_a_758_, v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go(lean_object* v_m_763_, lean_object* v_00_u03b1_764_, lean_object* v_inst_765_, lean_object* v_f_766_, lean_object* v_ctx_x3f_767_, lean_object* v_a_768_, lean_object* v_x_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg(v_inst_765_, v_f_766_, v_ctx_x3f_767_, v_a_768_, v_x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___redArg(lean_object* v_inst_771_, lean_object* v_f_772_, lean_object* v_init_773_, lean_object* v_x_774_){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_box(0);
v___x_776_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoM_go___redArg(v_inst_771_, v_f_772_, v___x_775_, v_init_773_, v_x_774_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM(lean_object* v_m_777_, lean_object* v_00_u03b1_778_, lean_object* v_inst_779_, lean_object* v_f_780_, lean_object* v_init_781_, lean_object* v_x_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_Elab_InfoTree_foldInfoM___redArg(v_inst_779_, v_f_780_, v_init_781_, v_x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(lean_object* v_f_784_, lean_object* v___x_785_, lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
if (lean_obj_tag(v_x_786_) == 0)
{
lean_object* v_cs_788_; lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v_cs_788_ = lean_ctor_get(v_x_786_, 0);
v___x_789_ = lean_unsigned_to_nat(0u);
v___x_790_ = lean_array_get_size(v_cs_788_);
v___x_791_ = lean_nat_dec_lt(v___x_789_, v___x_790_);
if (v___x_791_ == 0)
{
lean_dec(v___x_785_);
lean_dec(v_f_784_);
return v_x_787_;
}
else
{
uint8_t v___x_792_; 
v___x_792_ = lean_nat_dec_le(v___x_790_, v___x_790_);
if (v___x_792_ == 0)
{
if (v___x_791_ == 0)
{
lean_dec(v___x_785_);
lean_dec(v_f_784_);
return v_x_787_;
}
else
{
size_t v___x_793_; size_t v___x_794_; lean_object* v___x_795_; 
v___x_793_ = ((size_t)0ULL);
v___x_794_ = lean_usize_of_nat(v___x_790_);
v___x_795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_784_, v___x_785_, v_cs_788_, v___x_793_, v___x_794_, v_x_787_);
return v___x_795_;
}
}
else
{
size_t v___x_796_; size_t v___x_797_; lean_object* v___x_798_; 
v___x_796_ = ((size_t)0ULL);
v___x_797_ = lean_usize_of_nat(v___x_790_);
v___x_798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_784_, v___x_785_, v_cs_788_, v___x_796_, v___x_797_, v_x_787_);
return v___x_798_;
}
}
}
else
{
lean_object* v_vs_799_; lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v_vs_799_ = lean_ctor_get(v_x_786_, 0);
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_array_get_size(v_vs_799_);
v___x_802_ = lean_nat_dec_lt(v___x_800_, v___x_801_);
if (v___x_802_ == 0)
{
lean_dec(v___x_785_);
lean_dec(v_f_784_);
return v_x_787_;
}
else
{
uint8_t v___x_803_; 
v___x_803_ = lean_nat_dec_le(v___x_801_, v___x_801_);
if (v___x_803_ == 0)
{
if (v___x_802_ == 0)
{
lean_dec(v___x_785_);
lean_dec(v_f_784_);
return v_x_787_;
}
else
{
size_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; 
v___x_804_ = ((size_t)0ULL);
v___x_805_ = lean_usize_of_nat(v___x_801_);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_784_, v___x_785_, v_vs_799_, v___x_804_, v___x_805_, v_x_787_);
return v___x_806_;
}
}
else
{
size_t v___x_807_; size_t v___x_808_; lean_object* v___x_809_; 
v___x_807_ = ((size_t)0ULL);
v___x_808_ = lean_usize_of_nat(v___x_801_);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_784_, v___x_785_, v_vs_799_, v___x_807_, v___x_808_, v_x_787_);
return v___x_809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(lean_object* v_f_810_, lean_object* v___x_811_, lean_object* v_as_812_, size_t v_i_813_, size_t v_stop_814_, lean_object* v_b_815_){
_start:
{
uint8_t v___x_816_; 
v___x_816_ = lean_usize_dec_eq(v_i_813_, v_stop_814_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; lean_object* v___x_818_; size_t v___x_819_; size_t v___x_820_; 
v___x_817_ = lean_array_uget_borrowed(v_as_812_, v_i_813_);
lean_inc(v___x_811_);
lean_inc(v_f_810_);
v___x_818_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(v_f_810_, v___x_811_, v___x_817_, v_b_815_);
v___x_819_ = ((size_t)1ULL);
v___x_820_ = lean_usize_add(v_i_813_, v___x_819_);
v_i_813_ = v___x_820_;
v_b_815_ = v___x_818_;
goto _start;
}
else
{
lean_dec(v___x_811_);
lean_dec(v_f_810_);
return v_b_815_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(lean_object* v_f_822_, lean_object* v___x_823_, lean_object* v_x_824_, size_t v_x_825_, size_t v_x_826_, lean_object* v_x_827_){
_start:
{
if (lean_obj_tag(v_x_824_) == 0)
{
lean_object* v_cs_828_; lean_object* v___x_829_; size_t v___x_830_; lean_object* v_j_831_; lean_object* v___x_832_; size_t v___x_833_; size_t v___x_834_; size_t v___x_835_; size_t v___x_836_; size_t v___x_837_; size_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v_cs_828_ = lean_ctor_get(v_x_824_, 0);
v___x_829_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0);
v___x_830_ = lean_usize_shift_right(v_x_825_, v_x_826_);
v_j_831_ = lean_usize_to_nat(v___x_830_);
v___x_832_ = lean_array_get_borrowed(v___x_829_, v_cs_828_, v_j_831_);
v___x_833_ = ((size_t)1ULL);
v___x_834_ = lean_usize_shift_left(v___x_833_, v_x_826_);
v___x_835_ = lean_usize_sub(v___x_834_, v___x_833_);
v___x_836_ = lean_usize_land(v_x_825_, v___x_835_);
v___x_837_ = ((size_t)5ULL);
v___x_838_ = lean_usize_sub(v_x_826_, v___x_837_);
lean_inc(v___x_823_);
lean_inc(v_f_822_);
v___x_839_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(v_f_822_, v___x_823_, v___x_832_, v___x_836_, v___x_838_, v_x_827_);
v___x_840_ = lean_unsigned_to_nat(1u);
v___x_841_ = lean_nat_add(v_j_831_, v___x_840_);
lean_dec(v_j_831_);
v___x_842_ = lean_array_get_size(v_cs_828_);
v___x_843_ = lean_nat_dec_lt(v___x_841_, v___x_842_);
if (v___x_843_ == 0)
{
lean_dec(v___x_841_);
lean_dec(v___x_823_);
lean_dec(v_f_822_);
return v___x_839_;
}
else
{
uint8_t v___x_844_; 
v___x_844_ = lean_nat_dec_le(v___x_842_, v___x_842_);
if (v___x_844_ == 0)
{
if (v___x_843_ == 0)
{
lean_dec(v___x_841_);
lean_dec(v___x_823_);
lean_dec(v_f_822_);
return v___x_839_;
}
else
{
size_t v___x_845_; size_t v___x_846_; lean_object* v___x_847_; 
v___x_845_ = lean_usize_of_nat(v___x_841_);
lean_dec(v___x_841_);
v___x_846_ = lean_usize_of_nat(v___x_842_);
v___x_847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_822_, v___x_823_, v_cs_828_, v___x_845_, v___x_846_, v___x_839_);
return v___x_847_;
}
}
else
{
size_t v___x_848_; size_t v___x_849_; lean_object* v___x_850_; 
v___x_848_ = lean_usize_of_nat(v___x_841_);
lean_dec(v___x_841_);
v___x_849_ = lean_usize_of_nat(v___x_842_);
v___x_850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_822_, v___x_823_, v_cs_828_, v___x_848_, v___x_849_, v___x_839_);
return v___x_850_;
}
}
}
else
{
lean_object* v_vs_851_; lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v_vs_851_ = lean_ctor_get(v_x_824_, 0);
v___x_852_ = lean_usize_to_nat(v_x_825_);
v___x_853_ = lean_array_get_size(v_vs_851_);
v___x_854_ = lean_nat_dec_lt(v___x_852_, v___x_853_);
if (v___x_854_ == 0)
{
lean_dec(v___x_852_);
lean_dec(v___x_823_);
lean_dec(v_f_822_);
return v_x_827_;
}
else
{
uint8_t v___x_855_; 
v___x_855_ = lean_nat_dec_le(v___x_853_, v___x_853_);
if (v___x_855_ == 0)
{
if (v___x_854_ == 0)
{
lean_dec(v___x_852_);
lean_dec(v___x_823_);
lean_dec(v_f_822_);
return v_x_827_;
}
else
{
size_t v___x_856_; size_t v___x_857_; lean_object* v___x_858_; 
v___x_856_ = lean_usize_of_nat(v___x_852_);
lean_dec(v___x_852_);
v___x_857_ = lean_usize_of_nat(v___x_853_);
v___x_858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_822_, v___x_823_, v_vs_851_, v___x_856_, v___x_857_, v_x_827_);
return v___x_858_;
}
}
else
{
size_t v___x_859_; size_t v___x_860_; lean_object* v___x_861_; 
v___x_859_ = lean_usize_of_nat(v___x_852_);
lean_dec(v___x_852_);
v___x_860_ = lean_usize_of_nat(v___x_853_);
v___x_861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_822_, v___x_823_, v_vs_851_, v___x_859_, v___x_860_, v_x_827_);
return v___x_861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(lean_object* v_f_862_, lean_object* v___x_863_, lean_object* v_t_864_, lean_object* v_init_865_, lean_object* v_start_866_){
_start:
{
lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_867_ = lean_unsigned_to_nat(0u);
v___x_868_ = lean_nat_dec_eq(v_start_866_, v___x_867_);
if (v___x_868_ == 0)
{
lean_object* v_root_869_; lean_object* v_tail_870_; size_t v_shift_871_; lean_object* v_tailOff_872_; uint8_t v___x_873_; 
v_root_869_ = lean_ctor_get(v_t_864_, 0);
v_tail_870_ = lean_ctor_get(v_t_864_, 1);
v_shift_871_ = lean_ctor_get_usize(v_t_864_, 4);
v_tailOff_872_ = lean_ctor_get(v_t_864_, 3);
v___x_873_ = lean_nat_dec_le(v_tailOff_872_, v_start_866_);
if (v___x_873_ == 0)
{
size_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v___x_874_ = lean_usize_of_nat(v_start_866_);
lean_inc(v___x_863_);
lean_inc(v_f_862_);
v___x_875_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(v_f_862_, v___x_863_, v_root_869_, v___x_874_, v_shift_871_, v_init_865_);
v___x_876_ = lean_array_get_size(v_tail_870_);
v___x_877_ = lean_nat_dec_lt(v___x_867_, v___x_876_);
if (v___x_877_ == 0)
{
lean_dec(v___x_863_);
lean_dec(v_f_862_);
return v___x_875_;
}
else
{
uint8_t v___x_878_; 
v___x_878_ = lean_nat_dec_le(v___x_876_, v___x_876_);
if (v___x_878_ == 0)
{
if (v___x_877_ == 0)
{
lean_dec(v___x_863_);
lean_dec(v_f_862_);
return v___x_875_;
}
else
{
size_t v___x_879_; size_t v___x_880_; lean_object* v___x_881_; 
v___x_879_ = ((size_t)0ULL);
v___x_880_ = lean_usize_of_nat(v___x_876_);
v___x_881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_862_, v___x_863_, v_tail_870_, v___x_879_, v___x_880_, v___x_875_);
return v___x_881_;
}
}
else
{
size_t v___x_882_; size_t v___x_883_; lean_object* v___x_884_; 
v___x_882_ = ((size_t)0ULL);
v___x_883_ = lean_usize_of_nat(v___x_876_);
v___x_884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_862_, v___x_863_, v_tail_870_, v___x_882_, v___x_883_, v___x_875_);
return v___x_884_;
}
}
}
else
{
lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_885_ = lean_nat_sub(v_start_866_, v_tailOff_872_);
v___x_886_ = lean_array_get_size(v_tail_870_);
v___x_887_ = lean_nat_dec_lt(v___x_885_, v___x_886_);
if (v___x_887_ == 0)
{
lean_dec(v___x_885_);
lean_dec(v___x_863_);
lean_dec(v_f_862_);
return v_init_865_;
}
else
{
uint8_t v___x_888_; 
v___x_888_ = lean_nat_dec_le(v___x_886_, v___x_886_);
if (v___x_888_ == 0)
{
if (v___x_887_ == 0)
{
lean_dec(v___x_885_);
lean_dec(v___x_863_);
lean_dec(v_f_862_);
return v_init_865_;
}
else
{
size_t v___x_889_; size_t v___x_890_; lean_object* v___x_891_; 
v___x_889_ = lean_usize_of_nat(v___x_885_);
lean_dec(v___x_885_);
v___x_890_ = lean_usize_of_nat(v___x_886_);
v___x_891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_862_, v___x_863_, v_tail_870_, v___x_889_, v___x_890_, v_init_865_);
return v___x_891_;
}
}
else
{
size_t v___x_892_; size_t v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_usize_of_nat(v___x_885_);
lean_dec(v___x_885_);
v___x_893_ = lean_usize_of_nat(v___x_886_);
v___x_894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_862_, v___x_863_, v_tail_870_, v___x_892_, v___x_893_, v_init_865_);
return v___x_894_;
}
}
}
}
else
{
lean_object* v_root_895_; lean_object* v_tail_896_; lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v_root_895_ = lean_ctor_get(v_t_864_, 0);
v_tail_896_ = lean_ctor_get(v_t_864_, 1);
lean_inc(v___x_863_);
lean_inc(v_f_862_);
v___x_897_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(v_f_862_, v___x_863_, v_root_895_, v_init_865_);
v___x_898_ = lean_array_get_size(v_tail_896_);
v___x_899_ = lean_nat_dec_lt(v___x_867_, v___x_898_);
if (v___x_899_ == 0)
{
lean_dec(v___x_863_);
lean_dec(v_f_862_);
return v___x_897_;
}
else
{
uint8_t v___x_900_; 
v___x_900_ = lean_nat_dec_le(v___x_898_, v___x_898_);
if (v___x_900_ == 0)
{
if (v___x_899_ == 0)
{
lean_dec(v___x_863_);
lean_dec(v_f_862_);
return v___x_897_;
}
else
{
size_t v___x_901_; size_t v___x_902_; lean_object* v___x_903_; 
v___x_901_ = ((size_t)0ULL);
v___x_902_ = lean_usize_of_nat(v___x_898_);
v___x_903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_862_, v___x_863_, v_tail_896_, v___x_901_, v___x_902_, v___x_897_);
return v___x_903_;
}
}
else
{
size_t v___x_904_; size_t v___x_905_; lean_object* v___x_906_; 
v___x_904_ = ((size_t)0ULL);
v___x_905_ = lean_usize_of_nat(v___x_898_);
v___x_906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_862_, v___x_863_, v_tail_896_, v___x_904_, v___x_905_, v___x_897_);
return v___x_906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(lean_object* v_f_907_, lean_object* v_ctx_x3f_908_, lean_object* v_a_909_, lean_object* v_x_910_){
_start:
{
switch(lean_obj_tag(v_x_910_))
{
case 0:
{
lean_object* v_i_911_; lean_object* v_t_912_; lean_object* v___x_913_; 
v_i_911_ = lean_ctor_get(v_x_910_, 0);
lean_inc_ref(v_i_911_);
v_t_912_ = lean_ctor_get(v_x_910_, 1);
lean_inc_ref(v_t_912_);
lean_dec_ref_known(v_x_910_, 2);
v___x_913_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_911_, v_ctx_x3f_908_);
v_ctx_x3f_908_ = v___x_913_;
v_x_910_ = v_t_912_;
goto _start;
}
case 1:
{
lean_object* v_i_915_; lean_object* v_children_916_; lean_object* v___y_918_; 
v_i_915_ = lean_ctor_get(v_x_910_, 0);
lean_inc_ref(v_i_915_);
v_children_916_ = lean_ctor_get(v_x_910_, 1);
lean_inc_ref(v_children_916_);
if (lean_obj_tag(v_ctx_x3f_908_) == 0)
{
lean_dec_ref_known(v_x_910_, 2);
v___y_918_ = v_a_909_;
goto v___jp_917_;
}
else
{
lean_object* v_val_922_; lean_object* v___x_923_; 
v_val_922_ = lean_ctor_get(v_ctx_x3f_908_, 0);
lean_inc(v_f_907_);
lean_inc(v_val_922_);
v___x_923_ = lean_apply_3(v_f_907_, v_val_922_, v_x_910_, v_a_909_);
v___y_918_ = v___x_923_;
goto v___jp_917_;
}
v___jp_917_:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_919_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_908_, v_i_915_);
lean_dec_ref(v_i_915_);
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(v_f_907_, v___x_919_, v_children_916_, v___y_918_, v___x_920_);
lean_dec_ref(v_children_916_);
return v___x_921_;
}
}
default: 
{
lean_dec_ref_known(v_x_910_, 1);
lean_dec(v_ctx_x3f_908_);
lean_dec(v_f_907_);
return v_a_909_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(lean_object* v_f_924_, lean_object* v___x_925_, lean_object* v_as_926_, size_t v_i_927_, size_t v_stop_928_, lean_object* v_b_929_){
_start:
{
uint8_t v___x_930_; 
v___x_930_ = lean_usize_dec_eq(v_i_927_, v_stop_928_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; size_t v___x_933_; size_t v___x_934_; 
v___x_931_ = lean_array_uget_borrowed(v_as_926_, v_i_927_);
lean_inc(v___x_931_);
lean_inc(v___x_925_);
lean_inc(v_f_924_);
v___x_932_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(v_f_924_, v___x_925_, v_b_929_, v___x_931_);
v___x_933_ = ((size_t)1ULL);
v___x_934_ = lean_usize_add(v_i_927_, v___x_933_);
v_i_927_ = v___x_934_;
v_b_929_ = v___x_932_;
goto _start;
}
else
{
lean_dec(v___x_925_);
lean_dec(v_f_924_);
return v_b_929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg___boxed(lean_object* v_f_936_, lean_object* v___x_937_, lean_object* v_as_938_, lean_object* v_i_939_, lean_object* v_stop_940_, lean_object* v_b_941_){
_start:
{
size_t v_i_boxed_942_; size_t v_stop_boxed_943_; lean_object* v_res_944_; 
v_i_boxed_942_ = lean_unbox_usize(v_i_939_);
lean_dec(v_i_939_);
v_stop_boxed_943_ = lean_unbox_usize(v_stop_940_);
lean_dec(v_stop_940_);
v_res_944_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_936_, v___x_937_, v_as_938_, v_i_boxed_942_, v_stop_boxed_943_, v_b_941_);
lean_dec_ref(v_as_938_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_945_, lean_object* v___x_946_, lean_object* v_as_947_, lean_object* v_i_948_, lean_object* v_stop_949_, lean_object* v_b_950_){
_start:
{
size_t v_i_boxed_951_; size_t v_stop_boxed_952_; lean_object* v_res_953_; 
v_i_boxed_951_ = lean_unbox_usize(v_i_948_);
lean_dec(v_i_948_);
v_stop_boxed_952_ = lean_unbox_usize(v_stop_949_);
lean_dec(v_stop_949_);
v_res_953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_945_, v___x_946_, v_as_947_, v_i_boxed_951_, v_stop_boxed_952_, v_b_950_);
lean_dec_ref(v_as_947_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg___boxed(lean_object* v_f_954_, lean_object* v___x_955_, lean_object* v_x_956_, lean_object* v_x_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(v_f_954_, v___x_955_, v_x_956_, v_x_957_);
lean_dec_ref(v_x_956_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg___boxed(lean_object* v_f_959_, lean_object* v___x_960_, lean_object* v_x_961_, lean_object* v_x_962_, lean_object* v_x_963_, lean_object* v_x_964_){
_start:
{
size_t v_x_1544__boxed_965_; size_t v_x_1545__boxed_966_; lean_object* v_res_967_; 
v_x_1544__boxed_965_ = lean_unbox_usize(v_x_962_);
lean_dec(v_x_962_);
v_x_1545__boxed_966_ = lean_unbox_usize(v_x_963_);
lean_dec(v_x_963_);
v_res_967_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(v_f_959_, v___x_960_, v_x_961_, v_x_1544__boxed_965_, v_x_1545__boxed_966_, v_x_964_);
lean_dec_ref(v_x_961_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg___boxed(lean_object* v_f_968_, lean_object* v___x_969_, lean_object* v_t_970_, lean_object* v_init_971_, lean_object* v_start_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(v_f_968_, v___x_969_, v_t_970_, v_init_971_, v_start_972_);
lean_dec(v_start_972_);
lean_dec_ref(v_t_970_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go(lean_object* v_00_u03b1_974_, lean_object* v_f_975_, lean_object* v_ctx_x3f_976_, lean_object* v_a_977_, lean_object* v_x_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(v_f_975_, v_ctx_x3f_976_, v_a_977_, v_x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0(lean_object* v_00_u03b1_980_, lean_object* v_f_981_, lean_object* v___x_982_, lean_object* v_t_983_, lean_object* v_init_984_, lean_object* v_start_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(v_f_981_, v___x_982_, v_t_983_, v_init_984_, v_start_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___boxed(lean_object* v_00_u03b1_987_, lean_object* v_f_988_, lean_object* v___x_989_, lean_object* v_t_990_, lean_object* v_init_991_, lean_object* v_start_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0(v_00_u03b1_987_, v_f_988_, v___x_989_, v_t_990_, v_init_991_, v_start_992_);
lean_dec(v_start_992_);
lean_dec_ref(v_t_990_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0(lean_object* v_00_u03b1_994_, lean_object* v_f_995_, lean_object* v___x_996_, lean_object* v_x_997_, size_t v_x_998_, size_t v_x_999_, lean_object* v_x_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(v_f_995_, v___x_996_, v_x_997_, v_x_998_, v_x_999_, v_x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1002_, lean_object* v_f_1003_, lean_object* v___x_1004_, lean_object* v_x_1005_, lean_object* v_x_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_){
_start:
{
size_t v_x_1763__boxed_1009_; size_t v_x_1764__boxed_1010_; lean_object* v_res_1011_; 
v_x_1763__boxed_1009_ = lean_unbox_usize(v_x_1006_);
lean_dec(v_x_1006_);
v_x_1764__boxed_1010_ = lean_unbox_usize(v_x_1007_);
lean_dec(v_x_1007_);
v_res_1011_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0(v_00_u03b1_1002_, v_f_1003_, v___x_1004_, v_x_1005_, v_x_1763__boxed_1009_, v_x_1764__boxed_1010_, v_x_1008_);
lean_dec_ref(v_x_1005_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1(lean_object* v_00_u03b1_1012_, lean_object* v_f_1013_, lean_object* v___x_1014_, lean_object* v_as_1015_, size_t v_i_1016_, size_t v_stop_1017_, lean_object* v_b_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_1013_, v___x_1014_, v_as_1015_, v_i_1016_, v_stop_1017_, v_b_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1020_, lean_object* v_f_1021_, lean_object* v___x_1022_, lean_object* v_as_1023_, lean_object* v_i_1024_, lean_object* v_stop_1025_, lean_object* v_b_1026_){
_start:
{
size_t v_i_boxed_1027_; size_t v_stop_boxed_1028_; lean_object* v_res_1029_; 
v_i_boxed_1027_ = lean_unbox_usize(v_i_1024_);
lean_dec(v_i_1024_);
v_stop_boxed_1028_ = lean_unbox_usize(v_stop_1025_);
lean_dec(v_stop_1025_);
v_res_1029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1(v_00_u03b1_1020_, v_f_1021_, v___x_1022_, v_as_1023_, v_i_boxed_1027_, v_stop_boxed_1028_, v_b_1026_);
lean_dec_ref(v_as_1023_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2(lean_object* v_00_u03b1_1030_, lean_object* v_f_1031_, lean_object* v___x_1032_, lean_object* v_x_1033_, lean_object* v_x_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(v_f_1031_, v___x_1032_, v_x_1033_, v_x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1036_, lean_object* v_f_1037_, lean_object* v___x_1038_, lean_object* v_x_1039_, lean_object* v_x_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2(v_00_u03b1_1036_, v_f_1037_, v___x_1038_, v_x_1039_, v_x_1040_);
lean_dec_ref(v_x_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1042_, lean_object* v_f_1043_, lean_object* v___x_1044_, lean_object* v_as_1045_, size_t v_i_1046_, size_t v_stop_1047_, lean_object* v_b_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_1043_, v___x_1044_, v_as_1045_, v_i_1046_, v_stop_1047_, v_b_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1050_, lean_object* v_f_1051_, lean_object* v___x_1052_, lean_object* v_as_1053_, lean_object* v_i_1054_, lean_object* v_stop_1055_, lean_object* v_b_1056_){
_start:
{
size_t v_i_boxed_1057_; size_t v_stop_boxed_1058_; lean_object* v_res_1059_; 
v_i_boxed_1057_ = lean_unbox_usize(v_i_1054_);
lean_dec(v_i_1054_);
v_stop_boxed_1058_ = lean_unbox_usize(v_stop_1055_);
lean_dec(v_stop_1055_);
v_res_1059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1(v_00_u03b1_1050_, v_f_1051_, v___x_1052_, v_as_1053_, v_i_boxed_1057_, v_stop_boxed_1058_, v_b_1056_);
lean_dec_ref(v_as_1053_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoTree___redArg(lean_object* v_init_1060_, lean_object* v_f_1061_, lean_object* v_x_1062_){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_box(0);
v___x_1064_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(v_f_1061_, v___x_1063_, v_init_1060_, v_x_1062_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoTree(lean_object* v_00_u03b1_1065_, lean_object* v_init_1066_, lean_object* v_f_1067_, lean_object* v_x_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_Elab_InfoTree_foldInfoTree___redArg(v_init_1066_, v_f_1067_, v_x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0(lean_object* v_toPure_1070_, lean_object* v_result_1071_, lean_object* v_____do__lift_1072_){
_start:
{
if (lean_obj_tag(v_____do__lift_1072_) == 0)
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_apply_2(v_toPure_1070_, lean_box(0), v_result_1071_);
return v___x_1073_;
}
else
{
lean_object* v_val_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v_val_1074_ = lean_ctor_get(v_____do__lift_1072_, 0);
lean_inc(v_val_1074_);
v___x_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_val_1074_);
lean_ctor_set(v___x_1075_, 1, v_result_1071_);
v___x_1076_ = lean_apply_2(v_toPure_1070_, lean_box(0), v___x_1075_);
return v___x_1076_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0___boxed(lean_object* v_toPure_1077_, lean_object* v_result_1078_, lean_object* v_____do__lift_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0(v_toPure_1077_, v_result_1078_, v_____do__lift_1079_);
lean_dec(v_____do__lift_1079_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__1(lean_object* v_toPure_1081_, lean_object* v_f_1082_, lean_object* v_toBind_1083_, lean_object* v_ctx_1084_, lean_object* v_info_1085_, lean_object* v_result_1086_){
_start:
{
if (lean_obj_tag(v_info_1085_) == 1)
{
lean_object* v_i_1087_; lean_object* v___f_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_i_1087_ = lean_ctor_get(v_info_1085_, 0);
lean_inc_ref(v_i_1087_);
lean_dec_ref_known(v_info_1085_, 1);
v___f_1088_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1088_, 0, v_toPure_1081_);
lean_closure_set(v___f_1088_, 1, v_result_1086_);
v___x_1089_ = lean_apply_2(v_f_1082_, v_ctx_1084_, v_i_1087_);
v___x_1090_ = lean_apply_4(v_toBind_1083_, lean_box(0), lean_box(0), v___x_1089_, v___f_1088_);
return v___x_1090_;
}
else
{
lean_object* v___x_1091_; 
lean_dec_ref(v_info_1085_);
lean_dec_ref(v_ctx_1084_);
lean_dec(v_toBind_1083_);
lean_dec(v_f_1082_);
v___x_1091_ = lean_apply_2(v_toPure_1081_, lean_box(0), v_result_1086_);
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___redArg(lean_object* v_inst_1092_, lean_object* v_t_1093_, lean_object* v_f_1094_){
_start:
{
lean_object* v_toApplicative_1095_; lean_object* v_toBind_1096_; lean_object* v_toPure_1097_; lean_object* v___f_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v_toApplicative_1095_ = lean_ctor_get(v_inst_1092_, 0);
v_toBind_1096_ = lean_ctor_get(v_inst_1092_, 1);
v_toPure_1097_ = lean_ctor_get(v_toApplicative_1095_, 1);
lean_inc(v_toBind_1096_);
lean_inc(v_toPure_1097_);
v___f_1098_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__1), 6, 3);
lean_closure_set(v___f_1098_, 0, v_toPure_1097_);
lean_closure_set(v___f_1098_, 1, v_f_1094_);
lean_closure_set(v___f_1098_, 2, v_toBind_1096_);
v___x_1099_ = lean_box(0);
v___x_1100_ = l_Lean_Elab_InfoTree_foldInfoM___redArg(v_inst_1092_, v___f_1098_, v___x_1099_, v_t_1093_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM(lean_object* v_m_1101_, lean_object* v_00_u03b1_1102_, lean_object* v_inst_1103_, lean_object* v_t_1104_, lean_object* v_f_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Lean_Elab_InfoTree_collectTermInfoM___redArg(v_inst_1103_, v_t_1104_, v_f_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Info_isTerm(lean_object* v_x_1107_){
_start:
{
if (lean_obj_tag(v_x_1107_) == 1)
{
uint8_t v___x_1108_; 
v___x_1108_ = 1;
return v___x_1108_;
}
else
{
uint8_t v___x_1109_; 
v___x_1109_ = 0;
return v___x_1109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_isTerm___boxed(lean_object* v_x_1110_){
_start:
{
uint8_t v_res_1111_; lean_object* v_r_1112_; 
v_res_1111_ = l_Lean_Elab_Info_isTerm(v_x_1110_);
lean_dec_ref(v_x_1110_);
v_r_1112_ = lean_box(v_res_1111_);
return v_r_1112_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Info_isCompletion(lean_object* v_x_1113_){
_start:
{
if (lean_obj_tag(v_x_1113_) == 8)
{
uint8_t v___x_1114_; 
v___x_1114_ = 1;
return v___x_1114_;
}
else
{
uint8_t v___x_1115_; 
v___x_1115_ = 0;
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_isCompletion___boxed(lean_object* v_x_1116_){
_start:
{
uint8_t v_res_1117_; lean_object* v_r_1118_; 
v_res_1117_ = l_Lean_Elab_Info_isCompletion(v_x_1116_);
lean_dec_ref(v_x_1116_);
v_r_1118_ = lean_box(v_res_1117_);
return v_r_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_getCompletionInfos___lam__0(lean_object* v_ctx_1119_, lean_object* v_info_1120_, lean_object* v_result_1121_){
_start:
{
if (lean_obj_tag(v_info_1120_) == 8)
{
lean_object* v_i_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v_i_1122_ = lean_ctor_get(v_info_1120_, 0);
lean_inc_ref(v_i_1122_);
v___x_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1123_, 0, v_ctx_1119_);
lean_ctor_set(v___x_1123_, 1, v_i_1122_);
v___x_1124_ = lean_array_push(v_result_1121_, v___x_1123_);
return v___x_1124_;
}
else
{
lean_dec_ref(v_ctx_1119_);
return v_result_1121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_getCompletionInfos___lam__0___boxed(lean_object* v_ctx_1125_, lean_object* v_info_1126_, lean_object* v_result_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_Elab_InfoTree_getCompletionInfos___lam__0(v_ctx_1125_, v_info_1126_, v_result_1127_);
lean_dec_ref(v_info_1126_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_getCompletionInfos(lean_object* v_infoTree_1132_){
_start:
{
lean_object* v___f_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___f_1133_ = ((lean_object*)(l_Lean_Elab_InfoTree_getCompletionInfos___closed__0));
v___x_1134_ = ((lean_object*)(l_Lean_Elab_InfoTree_getCompletionInfos___closed__1));
v___x_1135_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_1133_, v___x_1134_, v_infoTree_1132_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_lctx(lean_object* v_x_1136_){
_start:
{
switch(lean_obj_tag(v_x_1136_))
{
case 1:
{
lean_object* v_i_1137_; lean_object* v_lctx_1138_; 
v_i_1137_ = lean_ctor_get(v_x_1136_, 0);
v_lctx_1138_ = lean_ctor_get(v_i_1137_, 1);
lean_inc_ref(v_lctx_1138_);
return v_lctx_1138_;
}
case 7:
{
lean_object* v_i_1139_; lean_object* v_lctx_1140_; 
v_i_1139_ = lean_ctor_get(v_x_1136_, 0);
v_lctx_1140_ = lean_ctor_get(v_i_1139_, 2);
lean_inc_ref(v_lctx_1140_);
return v_lctx_1140_;
}
case 13:
{
lean_object* v_i_1141_; lean_object* v_toTermInfo_1142_; lean_object* v_lctx_1143_; 
v_i_1141_ = lean_ctor_get(v_x_1136_, 0);
v_toTermInfo_1142_ = lean_ctor_get(v_i_1141_, 0);
v_lctx_1143_ = lean_ctor_get(v_toTermInfo_1142_, 1);
lean_inc_ref(v_lctx_1143_);
return v_lctx_1143_;
}
case 4:
{
lean_object* v_i_1144_; lean_object* v_lctx_1145_; 
v_i_1144_ = lean_ctor_get(v_x_1136_, 0);
v_lctx_1145_ = lean_ctor_get(v_i_1144_, 0);
lean_inc_ref(v_lctx_1145_);
return v_lctx_1145_;
}
case 8:
{
lean_object* v_i_1146_; lean_object* v___x_1147_; 
v_i_1146_ = lean_ctor_get(v_x_1136_, 0);
v___x_1147_ = l_Lean_Elab_CompletionInfo_lctx(v_i_1146_);
return v___x_1147_;
}
default: 
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_LocalContext_empty;
return v___x_1148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_lctx___boxed(lean_object* v_x_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_Elab_Info_lctx(v_x_1149_);
lean_dec_ref(v_x_1149_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_pos_x3f(lean_object* v_i_1151_){
_start:
{
lean_object* v___x_1152_; uint8_t v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = l_Lean_Elab_Info_stx(v_i_1151_);
v___x_1153_ = 1;
v___x_1154_ = l_Lean_Syntax_getPos_x3f(v___x_1152_, v___x_1153_);
lean_dec(v___x_1152_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_pos_x3f___boxed(lean_object* v_i_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_Elab_Info_pos_x3f(v_i_1155_);
lean_dec_ref(v_i_1155_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_tailPos_x3f(lean_object* v_i_1157_){
_start:
{
lean_object* v___x_1158_; uint8_t v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = l_Lean_Elab_Info_stx(v_i_1157_);
v___x_1159_ = 1;
v___x_1160_ = l_Lean_Syntax_getTailPos_x3f(v___x_1158_, v___x_1159_);
lean_dec(v___x_1158_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_tailPos_x3f___boxed(lean_object* v_i_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_Elab_Info_tailPos_x3f(v_i_1161_);
lean_dec_ref(v_i_1161_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_range_x3f(lean_object* v_i_1163_){
_start:
{
lean_object* v___x_1164_; uint8_t v___x_1165_; lean_object* v___x_1166_; 
v___x_1164_ = l_Lean_Elab_Info_stx(v_i_1163_);
v___x_1165_ = 1;
v___x_1166_ = l_Lean_Syntax_getRange_x3f(v___x_1164_, v___x_1165_);
lean_dec(v___x_1164_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_range_x3f___boxed(lean_object* v_i_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_Elab_Info_range_x3f(v_i_1167_);
lean_dec_ref(v_i_1167_);
return v_res_1168_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Info_contains(lean_object* v_i_1169_, lean_object* v_pos_1170_, uint8_t v_includeStop_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_Elab_Info_range_x3f(v_i_1169_);
if (lean_obj_tag(v___x_1172_) == 0)
{
uint8_t v___x_1173_; 
v___x_1173_ = 0;
return v___x_1173_;
}
else
{
lean_object* v_val_1174_; uint8_t v___x_1175_; 
v_val_1174_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_val_1174_);
lean_dec_ref_known(v___x_1172_, 1);
v___x_1175_ = l_Lean_Syntax_Range_contains(v_val_1174_, v_pos_1170_, v_includeStop_1171_);
lean_dec(v_val_1174_);
return v___x_1175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_contains___boxed(lean_object* v_i_1176_, lean_object* v_pos_1177_, lean_object* v_includeStop_1178_){
_start:
{
uint8_t v_includeStop_boxed_1179_; uint8_t v_res_1180_; lean_object* v_r_1181_; 
v_includeStop_boxed_1179_ = lean_unbox(v_includeStop_1178_);
v_res_1180_ = l_Lean_Elab_Info_contains(v_i_1176_, v_pos_1177_, v_includeStop_boxed_1179_);
lean_dec(v_pos_1177_);
lean_dec_ref(v_i_1176_);
v_r_1181_ = lean_box(v_res_1180_);
return v_r_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_size_x3f(lean_object* v_i_1182_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_Elab_Info_pos_x3f(v_i_1182_);
if (lean_obj_tag(v___x_1183_) == 0)
{
return v___x_1183_;
}
else
{
lean_object* v_val_1184_; lean_object* v___x_1185_; 
v_val_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_val_1184_);
lean_dec_ref_known(v___x_1183_, 1);
v___x_1185_ = l_Lean_Elab_Info_tailPos_x3f(v_i_1182_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_dec(v_val_1184_);
return v___x_1185_;
}
else
{
lean_object* v_val_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1194_; 
v_val_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_val_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1190_ = lean_nat_sub(v_val_1186_, v_val_1184_);
lean_dec(v_val_1184_);
lean_dec(v_val_1186_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1190_);
v___x_1192_ = v___x_1188_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_size_x3f___boxed(lean_object* v_i_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_Elab_Info_size_x3f(v_i_1195_);
lean_dec_ref(v_i_1195_);
return v_res_1196_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Info_isSmaller(lean_object* v_i_u2081_1197_, lean_object* v_i_u2082_1198_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_Elab_Info_size_x3f(v_i_u2081_1197_);
if (lean_obj_tag(v___x_1199_) == 1)
{
lean_object* v_val_1200_; lean_object* v___x_1201_; 
v_val_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_val_1200_);
lean_dec_ref_known(v___x_1199_, 1);
v___x_1201_ = l_Lean_Elab_Info_size_x3f(v_i_u2082_1198_);
if (lean_obj_tag(v___x_1201_) == 0)
{
uint8_t v___x_1202_; 
lean_dec(v_val_1200_);
v___x_1202_ = 1;
return v___x_1202_;
}
else
{
lean_object* v_val_1203_; uint8_t v___x_1204_; 
v_val_1203_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_val_1203_);
lean_dec_ref_known(v___x_1201_, 1);
v___x_1204_ = lean_nat_dec_lt(v_val_1200_, v_val_1203_);
lean_dec(v_val_1203_);
lean_dec(v_val_1200_);
return v___x_1204_;
}
}
else
{
uint8_t v___x_1205_; 
lean_dec(v___x_1199_);
v___x_1205_ = 0;
return v___x_1205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_isSmaller___boxed(lean_object* v_i_u2081_1206_, lean_object* v_i_u2082_1207_){
_start:
{
uint8_t v_res_1208_; lean_object* v_r_1209_; 
v_res_1208_ = l_Lean_Elab_Info_isSmaller(v_i_u2081_1206_, v_i_u2082_1207_);
lean_dec_ref(v_i_u2082_1207_);
lean_dec_ref(v_i_u2081_1206_);
v_r_1209_ = lean_box(v_res_1208_);
return v_r_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_occursInside_x3f(lean_object* v_i_1210_, lean_object* v_hoverPos_1211_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_Lean_Elab_Info_pos_x3f(v_i_1210_);
if (lean_obj_tag(v___x_1212_) == 0)
{
return v___x_1212_;
}
else
{
lean_object* v_val_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1228_; 
v_val_1213_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1215_ = v___x_1212_;
v_isShared_1216_ = v_isSharedCheck_1228_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_val_1213_);
lean_dec(v___x_1212_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1228_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
uint8_t v___y_1218_; lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_Elab_Info_tailPos_x3f(v_i_1210_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_del_object(v___x_1215_);
lean_dec(v_val_1213_);
return v___x_1224_;
}
else
{
lean_object* v_val_1225_; uint8_t v___x_1226_; 
v_val_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_val_1225_);
lean_dec_ref_known(v___x_1224_, 1);
v___x_1226_ = lean_nat_dec_le(v_val_1213_, v_hoverPos_1211_);
if (v___x_1226_ == 0)
{
lean_dec(v_val_1225_);
v___y_1218_ = v___x_1226_;
goto v___jp_1217_;
}
else
{
uint8_t v___x_1227_; 
v___x_1227_ = lean_nat_dec_lt(v_hoverPos_1211_, v_val_1225_);
lean_dec(v_val_1225_);
v___y_1218_ = v___x_1227_;
goto v___jp_1217_;
}
}
v___jp_1217_:
{
if (v___y_1218_ == 0)
{
lean_object* v___x_1219_; 
lean_del_object(v___x_1215_);
lean_dec(v_val_1213_);
v___x_1219_ = lean_box(0);
return v___x_1219_;
}
else
{
lean_object* v___x_1220_; lean_object* v___x_1222_; 
v___x_1220_ = lean_nat_sub(v_hoverPos_1211_, v_val_1213_);
lean_dec(v_val_1213_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1220_);
v___x_1222_ = v___x_1215_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_occursInside_x3f___boxed(lean_object* v_i_1229_, lean_object* v_hoverPos_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_Elab_Info_occursInside_x3f(v_i_1229_, v_hoverPos_1230_);
lean_dec(v_hoverPos_1230_);
lean_dec_ref(v_i_1229_);
return v_res_1231_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Info_occursInOrOnBoundary(lean_object* v_i_1232_, lean_object* v_hoverPos_1233_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_Elab_Info_pos_x3f(v_i_1232_);
if (lean_obj_tag(v___x_1234_) == 1)
{
lean_object* v_val_1235_; lean_object* v___x_1236_; 
v_val_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_val_1235_);
lean_dec_ref_known(v___x_1234_, 1);
v___x_1236_ = l_Lean_Elab_Info_tailPos_x3f(v_i_1232_);
if (lean_obj_tag(v___x_1236_) == 1)
{
lean_object* v_val_1237_; uint8_t v___x_1238_; 
v_val_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_val_1237_);
lean_dec_ref_known(v___x_1236_, 1);
v___x_1238_ = lean_nat_dec_le(v_val_1235_, v_hoverPos_1233_);
lean_dec(v_val_1235_);
if (v___x_1238_ == 0)
{
lean_dec(v_val_1237_);
return v___x_1238_;
}
else
{
uint8_t v___x_1239_; 
v___x_1239_ = lean_nat_dec_le(v_hoverPos_1233_, v_val_1237_);
lean_dec(v_val_1237_);
return v___x_1239_;
}
}
else
{
uint8_t v___x_1240_; 
lean_dec(v___x_1236_);
lean_dec(v_val_1235_);
v___x_1240_ = 0;
return v___x_1240_;
}
}
else
{
uint8_t v___x_1241_; 
lean_dec(v___x_1234_);
v___x_1241_ = 0;
return v___x_1241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_occursInOrOnBoundary___boxed(lean_object* v_i_1242_, lean_object* v_hoverPos_1243_){
_start:
{
uint8_t v_res_1244_; lean_object* v_r_1245_; 
v_res_1244_ = l_Lean_Elab_Info_occursInOrOnBoundary(v_i_1242_, v_hoverPos_1243_);
lean_dec(v_hoverPos_1243_);
lean_dec_ref(v_i_1242_);
v_r_1245_ = lean_box(v_res_1244_);
return v_r_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0(lean_object* v_p_1246_, lean_object* v_ctx_1247_, lean_object* v_i_1248_, lean_object* v_x_1249_){
_start:
{
lean_object* v___x_1250_; uint8_t v___x_1251_; 
lean_inc_ref(v_i_1248_);
v___x_1250_ = lean_apply_1(v_p_1246_, v_i_1248_);
v___x_1251_ = lean_unbox(v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; 
lean_dec_ref(v_i_1248_);
lean_dec_ref(v_ctx_1247_);
v___x_1252_ = lean_box(0);
return v___x_1252_;
}
else
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1253_, 0, v_ctx_1247_);
lean_ctor_set(v___x_1253_, 1, v_i_1248_);
v___x_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
return v___x_1254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0___boxed(lean_object* v_p_1255_, lean_object* v_ctx_1256_, lean_object* v_i_1257_, lean_object* v_x_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0(v_p_1255_, v_ctx_1256_, v_i_1257_, v_x_1258_);
lean_dec_ref(v_x_1258_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(lean_object* v_as_1260_, size_t v_i_1261_, size_t v_stop_1262_, lean_object* v_b_1263_){
_start:
{
lean_object* v___y_1265_; uint8_t v___x_1269_; 
v___x_1269_ = lean_usize_dec_eq(v_i_1261_, v_stop_1262_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; lean_object* v_fst_1271_; lean_object* v_fst_1272_; uint8_t v___x_1273_; 
v___x_1270_ = lean_array_uget_borrowed(v_as_1260_, v_i_1261_);
v_fst_1271_ = lean_ctor_get(v___x_1270_, 0);
v_fst_1272_ = lean_ctor_get(v_b_1263_, 0);
v___x_1273_ = lean_nat_dec_lt(v_fst_1271_, v_fst_1272_);
if (v___x_1273_ == 0)
{
v___y_1265_ = v_b_1263_;
goto v___jp_1264_;
}
else
{
v___y_1265_ = v___x_1270_;
goto v___jp_1264_;
}
}
else
{
lean_inc_ref(v_b_1263_);
return v_b_1263_;
}
v___jp_1264_:
{
size_t v___x_1266_; size_t v___x_1267_; 
v___x_1266_ = ((size_t)1ULL);
v___x_1267_ = lean_usize_add(v_i_1261_, v___x_1266_);
v_i_1261_ = v___x_1267_;
v_b_1263_ = v___y_1265_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1___boxed(lean_object* v_as_1274_, lean_object* v_i_1275_, lean_object* v_stop_1276_, lean_object* v_b_1277_){
_start:
{
size_t v_i_boxed_1278_; size_t v_stop_boxed_1279_; lean_object* v_res_1280_; 
v_i_boxed_1278_ = lean_unbox_usize(v_i_1275_);
lean_dec(v_i_1275_);
v_stop_boxed_1279_ = lean_unbox_usize(v_stop_1276_);
lean_dec(v_stop_1276_);
v_res_1280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(v_as_1274_, v_i_boxed_1278_, v_stop_boxed_1279_, v_b_1277_);
lean_dec_ref(v_b_1277_);
lean_dec_ref(v_as_1274_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1(lean_object* v_as_1281_){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1282_ = lean_unsigned_to_nat(0u);
v___x_1283_ = lean_array_get_size(v_as_1281_);
v___x_1284_ = lean_nat_dec_lt(v___x_1282_, v___x_1283_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_box(0);
return v___x_1285_;
}
else
{
lean_object* v_a0_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v_a0_1286_ = lean_array_fget_borrowed(v_as_1281_, v___x_1282_);
v___x_1287_ = lean_unsigned_to_nat(1u);
v___x_1288_ = lean_nat_dec_lt(v___x_1287_, v___x_1283_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; 
lean_inc(v_a0_1286_);
v___x_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1289_, 0, v_a0_1286_);
return v___x_1289_;
}
else
{
uint8_t v___x_1290_; 
v___x_1290_ = lean_nat_dec_le(v___x_1283_, v___x_1283_);
if (v___x_1290_ == 0)
{
if (v___x_1288_ == 0)
{
lean_object* v___x_1291_; 
lean_inc(v_a0_1286_);
v___x_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1291_, 0, v_a0_1286_);
return v___x_1291_;
}
else
{
size_t v___x_1292_; size_t v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1292_ = ((size_t)1ULL);
v___x_1293_ = lean_usize_of_nat(v___x_1283_);
v___x_1294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(v_as_1281_, v___x_1292_, v___x_1293_, v_a0_1286_);
v___x_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
return v___x_1295_;
}
}
else
{
size_t v___x_1296_; size_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1296_ = ((size_t)1ULL);
v___x_1297_ = lean_usize_of_nat(v___x_1283_);
v___x_1298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(v_as_1281_, v___x_1296_, v___x_1297_, v_a0_1286_);
v___x_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
return v___x_1299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1___boxed(lean_object* v_as_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1(v_as_1300_);
lean_dec_ref(v_as_1300_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__0(lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
if (lean_obj_tag(v_a_1302_) == 0)
{
lean_object* v___x_1304_; 
v___x_1304_ = lean_array_to_list(v_a_1303_);
return v___x_1304_;
}
else
{
lean_object* v_head_1305_; lean_object* v_tail_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1323_; 
v_head_1305_ = lean_ctor_get(v_a_1302_, 0);
v_tail_1306_ = lean_ctor_get(v_a_1302_, 1);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_a_1302_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1308_ = v_a_1302_;
v_isShared_1309_ = v_isSharedCheck_1323_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_tail_1306_);
lean_inc(v_head_1305_);
lean_dec(v_a_1302_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1323_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v_snd_1310_; lean_object* v___x_1311_; 
v_snd_1310_ = lean_ctor_get(v_head_1305_, 1);
v___x_1311_ = l_Lean_Elab_Info_pos_x3f(v_snd_1310_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_del_object(v___x_1308_);
lean_dec(v_head_1305_);
v_a_1302_ = v_tail_1306_;
goto _start;
}
else
{
lean_object* v_val_1313_; lean_object* v___x_1314_; 
v_val_1313_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_val_1313_);
lean_dec_ref_known(v___x_1311_, 1);
v___x_1314_ = l_Lean_Elab_Info_tailPos_x3f(v_snd_1310_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_dec(v_val_1313_);
lean_del_object(v___x_1308_);
lean_dec(v_head_1305_);
v_a_1302_ = v_tail_1306_;
goto _start;
}
else
{
lean_object* v_val_1316_; lean_object* v___x_1317_; lean_object* v___x_1319_; 
v_val_1316_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_val_1316_);
lean_dec_ref_known(v___x_1314_, 1);
v___x_1317_ = lean_nat_sub(v_val_1316_, v_val_1313_);
lean_dec(v_val_1313_);
lean_dec(v_val_1316_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set_tag(v___x_1308_, 0);
lean_ctor_set(v___x_1308_, 1, v_head_1305_);
lean_ctor_set(v___x_1308_, 0, v___x_1317_);
v___x_1319_ = v___x_1308_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_head_1305_);
v___x_1319_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_array_push(v_a_1303_, v___x_1319_);
v_a_1302_ = v_tail_1306_;
v_a_1303_ = v___x_1320_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f(lean_object* v_p_1326_, lean_object* v_t_1327_){
_start:
{
lean_object* v___f_1328_; lean_object* v_ts_1329_; lean_object* v___x_1330_; lean_object* v_infos_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___f_1328_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1328_, 0, v_p_1326_);
v_ts_1329_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_1328_, v_t_1327_);
v___x_1330_ = ((lean_object*)(l_Lean_Elab_InfoTree_smallestInfo_x3f___closed__0));
v_infos_1331_ = l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__0(v_ts_1329_, v___x_1330_);
v___x_1332_ = lean_array_mk(v_infos_1331_);
v___x_1333_ = l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1(v___x_1332_);
lean_dec_ref(v___x_1332_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_box(0);
return v___x_1334_;
}
else
{
lean_object* v_val_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1343_; 
v_val_1335_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1337_ = v___x_1333_;
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_val_1335_);
lean_dec(v___x_1333_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v_snd_1339_; lean_object* v___x_1341_; 
v_snd_1339_ = lean_ctor_get(v_val_1335_, 1);
lean_inc(v_snd_1339_);
lean_dec(v_val_1335_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v_snd_1339_);
v___x_1341_ = v___x_1337_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_snd_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_instBEqHoverableInfoPrio_beq(lean_object* v_x_1344_, lean_object* v_x_1345_){
_start:
{
uint8_t v_isHoverPosOnStop_1346_; lean_object* v_size_1347_; uint8_t v_isVariableInfo_1348_; uint8_t v_isPartialTermInfo_1349_; uint8_t v_isHoverPosOnStop_1350_; lean_object* v_size_1351_; uint8_t v_isVariableInfo_1352_; uint8_t v_isPartialTermInfo_1353_; uint8_t v___y_1355_; 
v_isHoverPosOnStop_1346_ = lean_ctor_get_uint8(v_x_1344_, sizeof(void*)*1);
v_size_1347_ = lean_ctor_get(v_x_1344_, 0);
v_isVariableInfo_1348_ = lean_ctor_get_uint8(v_x_1344_, sizeof(void*)*1 + 1);
v_isPartialTermInfo_1349_ = lean_ctor_get_uint8(v_x_1344_, sizeof(void*)*1 + 2);
v_isHoverPosOnStop_1350_ = lean_ctor_get_uint8(v_x_1345_, sizeof(void*)*1);
v_size_1351_ = lean_ctor_get(v_x_1345_, 0);
v_isVariableInfo_1352_ = lean_ctor_get_uint8(v_x_1345_, sizeof(void*)*1 + 1);
v_isPartialTermInfo_1353_ = lean_ctor_get_uint8(v_x_1345_, sizeof(void*)*1 + 2);
if (v_isHoverPosOnStop_1346_ == 0)
{
if (v_isHoverPosOnStop_1350_ == 0)
{
goto v___jp_1356_;
}
else
{
return v_isHoverPosOnStop_1346_;
}
}
else
{
if (v_isHoverPosOnStop_1350_ == 0)
{
return v_isHoverPosOnStop_1350_;
}
else
{
goto v___jp_1356_;
}
}
v___jp_1354_:
{
if (v___y_1355_ == 0)
{
return v___y_1355_;
}
else
{
if (v_isPartialTermInfo_1349_ == 0)
{
if (v_isPartialTermInfo_1353_ == 0)
{
return v___y_1355_;
}
else
{
return v_isPartialTermInfo_1349_;
}
}
else
{
return v_isPartialTermInfo_1353_;
}
}
}
v___jp_1356_:
{
uint8_t v___x_1357_; 
v___x_1357_ = lean_nat_dec_eq(v_size_1347_, v_size_1351_);
if (v___x_1357_ == 0)
{
return v___x_1357_;
}
else
{
if (v_isVariableInfo_1348_ == 0)
{
if (v_isVariableInfo_1352_ == 0)
{
v___y_1355_ = v___x_1357_;
goto v___jp_1354_;
}
else
{
return v_isVariableInfo_1348_;
}
}
else
{
v___y_1355_ = v_isVariableInfo_1352_;
goto v___jp_1354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instBEqHoverableInfoPrio_beq___boxed(lean_object* v_x_1358_, lean_object* v_x_1359_){
_start:
{
uint8_t v_res_1360_; lean_object* v_r_1361_; 
v_res_1360_ = l_Lean_Elab_instBEqHoverableInfoPrio_beq(v_x_1358_, v_x_1359_);
lean_dec_ref(v_x_1359_);
lean_dec_ref(v_x_1358_);
v_r_1361_ = lean_box(v_res_1360_);
return v_r_1361_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(lean_object* v_i1_1364_, lean_object* v_i2_1365_){
_start:
{
uint8_t v___y_1367_; uint8_t v___y_1371_; uint8_t v_isHoverPosOnStop_1374_; lean_object* v_size_1375_; uint8_t v_isVariableInfo_1376_; uint8_t v_isPartialTermInfo_1377_; uint8_t v___y_1379_; uint8_t v___y_1385_; uint8_t v___y_1386_; uint8_t v___y_1389_; 
v_isHoverPosOnStop_1374_ = lean_ctor_get_uint8(v_i1_1364_, sizeof(void*)*1);
v_size_1375_ = lean_ctor_get(v_i1_1364_, 0);
v_isVariableInfo_1376_ = lean_ctor_get_uint8(v_i1_1364_, sizeof(void*)*1 + 1);
v_isPartialTermInfo_1377_ = lean_ctor_get_uint8(v_i1_1364_, sizeof(void*)*1 + 2);
if (v_isHoverPosOnStop_1374_ == 0)
{
goto v___jp_1399_;
}
else
{
uint8_t v_isHoverPosOnStop_1402_; uint8_t v___x_1403_; 
v_isHoverPosOnStop_1402_ = lean_ctor_get_uint8(v_i2_1365_, sizeof(void*)*1);
v___x_1403_ = lean_bool_not(v_isHoverPosOnStop_1402_);
if (v___x_1403_ == 0)
{
goto v___jp_1399_;
}
else
{
uint8_t v___x_1404_; 
v___x_1404_ = 0;
return v___x_1404_;
}
}
v___jp_1366_:
{
if (v___y_1367_ == 0)
{
uint8_t v___x_1368_; 
v___x_1368_ = 1;
return v___x_1368_;
}
else
{
uint8_t v___x_1369_; 
v___x_1369_ = 2;
return v___x_1369_;
}
}
v___jp_1370_:
{
uint8_t v___x_1372_; 
v___x_1372_ = lean_bool_not(v___y_1371_);
if (v___x_1372_ == 0)
{
v___y_1367_ = v___x_1372_;
goto v___jp_1366_;
}
else
{
uint8_t v_isPartialTermInfo_1373_; 
v_isPartialTermInfo_1373_ = lean_ctor_get_uint8(v_i2_1365_, sizeof(void*)*1 + 2);
v___y_1367_ = v_isPartialTermInfo_1373_;
goto v___jp_1366_;
}
}
v___jp_1378_:
{
if (v___y_1379_ == 0)
{
if (v_isPartialTermInfo_1377_ == 0)
{
v___y_1371_ = v_isPartialTermInfo_1377_;
goto v___jp_1370_;
}
else
{
uint8_t v_isPartialTermInfo_1380_; uint8_t v___x_1381_; 
v_isPartialTermInfo_1380_ = lean_ctor_get_uint8(v_i2_1365_, sizeof(void*)*1 + 2);
v___x_1381_ = lean_bool_not(v_isPartialTermInfo_1380_);
if (v___x_1381_ == 0)
{
v___y_1371_ = v_isPartialTermInfo_1377_;
goto v___jp_1370_;
}
else
{
uint8_t v___x_1382_; 
v___x_1382_ = 0;
return v___x_1382_;
}
}
}
else
{
uint8_t v___x_1383_; 
v___x_1383_ = 2;
return v___x_1383_;
}
}
v___jp_1384_:
{
uint8_t v___x_1387_; 
v___x_1387_ = lean_bool_not(v___y_1385_);
if (v___x_1387_ == 0)
{
v___y_1379_ = v___x_1387_;
goto v___jp_1378_;
}
else
{
v___y_1379_ = v___y_1386_;
goto v___jp_1378_;
}
}
v___jp_1388_:
{
if (v___y_1389_ == 0)
{
lean_object* v_size_1390_; uint8_t v_isVariableInfo_1391_; uint8_t v___x_1392_; 
v_size_1390_ = lean_ctor_get(v_i2_1365_, 0);
v_isVariableInfo_1391_ = lean_ctor_get_uint8(v_i2_1365_, sizeof(void*)*1 + 1);
v___x_1392_ = lean_nat_dec_lt(v_size_1390_, v_size_1375_);
if (v___x_1392_ == 0)
{
uint8_t v___x_1393_; 
v___x_1393_ = lean_nat_dec_lt(v_size_1375_, v_size_1390_);
if (v___x_1393_ == 0)
{
if (v_isVariableInfo_1376_ == 0)
{
v___y_1385_ = v_isVariableInfo_1376_;
v___y_1386_ = v_isVariableInfo_1391_;
goto v___jp_1384_;
}
else
{
uint8_t v___x_1394_; 
v___x_1394_ = lean_bool_not(v_isVariableInfo_1391_);
if (v___x_1394_ == 0)
{
v___y_1385_ = v_isVariableInfo_1376_;
v___y_1386_ = v_isVariableInfo_1391_;
goto v___jp_1384_;
}
else
{
uint8_t v___x_1395_; 
v___x_1395_ = 0;
return v___x_1395_;
}
}
}
else
{
uint8_t v___x_1396_; 
v___x_1396_ = 2;
return v___x_1396_;
}
}
else
{
uint8_t v___x_1397_; 
v___x_1397_ = 0;
return v___x_1397_;
}
}
else
{
uint8_t v___x_1398_; 
v___x_1398_ = 2;
return v___x_1398_;
}
}
v___jp_1399_:
{
uint8_t v___x_1400_; 
v___x_1400_ = lean_bool_not(v_isHoverPosOnStop_1374_);
if (v___x_1400_ == 0)
{
v___y_1389_ = v___x_1400_;
goto v___jp_1388_;
}
else
{
uint8_t v_isHoverPosOnStop_1401_; 
v_isHoverPosOnStop_1401_ = lean_ctor_get_uint8(v_i2_1365_, sizeof(void*)*1);
v___y_1389_ = v_isHoverPosOnStop_1401_;
goto v___jp_1388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instOrdHoverableInfoPrio___lam__0___boxed(lean_object* v_i1_1405_, lean_object* v_i2_1406_){
_start:
{
uint8_t v_res_1407_; lean_object* v_r_1408_; 
v_res_1407_ = l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(v_i1_1405_, v_i2_1406_);
lean_dec_ref(v_i2_1406_);
lean_dec_ref(v_i1_1405_);
v_r_1408_ = lean_box(v_res_1407_);
return v_r_1408_;
}
}
static lean_object* _init_l_Lean_Elab_instLEHoverableInfoPrio(void){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = lean_box(0);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMaxHoverableInfoPrio___lam__0(lean_object* v_x_1412_, lean_object* v_y_1413_){
_start:
{
uint8_t v___x_1414_; 
v___x_1414_ = l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(v_x_1412_, v_y_1413_);
if (v___x_1414_ == 2)
{
lean_inc_ref(v_x_1412_);
return v_x_1412_;
}
else
{
lean_inc_ref(v_y_1413_);
return v_y_1413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMaxHoverableInfoPrio___lam__0___boxed(lean_object* v_x_1415_, lean_object* v_y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_Elab_instMaxHoverableInfoPrio___lam__0(v_x_1415_, v_y_1416_);
lean_dec_ref(v_y_1416_);
lean_dec_ref(v_x_1415_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0(lean_object* v_x_1420_){
_start:
{
lean_object* v_fst_1421_; 
v_fst_1421_ = lean_ctor_get(v_x_1420_, 0);
lean_inc(v_fst_1421_);
return v_fst_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0___boxed(lean_object* v_x_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0(v_x_1422_);
lean_dec_ref(v_x_1422_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1(lean_object* v_r_x3f_1424_){
_start:
{
if (lean_obj_tag(v_r_x3f_1424_) == 0)
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_box(0);
return v___x_1425_;
}
else
{
lean_object* v_val_1426_; 
v_val_1426_ = lean_ctor_get(v_r_x3f_1424_, 0);
lean_inc(v_val_1426_);
return v_val_1426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1___boxed(lean_object* v_r_x3f_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1(v_r_x3f_1427_);
lean_dec(v_r_x3f_1427_);
return v_res_1428_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2(lean_object* v___x_1429_, lean_object* v_maxPrio_x3f_1430_, lean_object* v_x_1431_){
_start:
{
lean_object* v_fst_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v_fst_1432_ = lean_ctor_get(v_x_1431_, 0);
lean_inc(v_fst_1432_);
v___x_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1433_, 0, v_fst_1432_);
v___x_1434_ = l_Option_instBEq_beq___redArg(v___x_1429_, v___x_1433_, v_maxPrio_x3f_1430_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2___boxed(lean_object* v___x_1435_, lean_object* v_maxPrio_x3f_1436_, lean_object* v_x_1437_){
_start:
{
uint8_t v_res_1438_; lean_object* v_r_1439_; 
v_res_1438_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2(v___x_1435_, v_maxPrio_x3f_1436_, v_x_1437_);
lean_dec_ref(v_x_1437_);
v_r_1439_ = lean_box(v_res_1438_);
return v_r_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3(lean_object* v___f_1452_, lean_object* v___f_1453_, lean_object* v___x_1454_, lean_object* v_toPure_1455_, lean_object* v_ctx_1456_, lean_object* v_info_1457_, lean_object* v_children_1458_, lean_object* v_hoverPos_1459_, uint8_t v_includeStop_1460_, lean_object* v_results_1461_){
_start:
{
uint8_t v___y_1463_; lean_object* v___y_1464_; uint8_t v___y_1465_; uint8_t v___y_1466_; uint8_t v___y_1473_; uint8_t v___y_1474_; lean_object* v___y_1475_; uint8_t v___y_1476_; uint8_t v___y_1477_; uint8_t v___y_1479_; lean_object* v___y_1480_; uint8_t v___y_1481_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v_maxPrio_x3f_1492_; lean_object* v___f_1493_; lean_object* v_bestResult_x3f_1494_; 
v___x_1490_ = lean_box(0);
lean_inc(v_results_1461_);
v___x_1491_ = l_List_mapTR_loop___redArg(v___f_1452_, v_results_1461_, v___x_1490_);
v_maxPrio_x3f_1492_ = l_List_max_x3f___redArg(v___f_1453_, v___x_1491_);
v___f_1493_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_1493_, 0, v___x_1454_);
lean_closure_set(v___f_1493_, 1, v_maxPrio_x3f_1492_);
v_bestResult_x3f_1494_ = l_List_find_x3f___redArg(v___f_1493_, v_results_1461_);
if (lean_obj_tag(v_bestResult_x3f_1494_) == 1)
{
lean_object* v___x_1495_; 
lean_dec_ref(v_children_1458_);
lean_dec_ref(v_info_1457_);
lean_dec_ref(v_ctx_1456_);
v___x_1495_ = lean_apply_2(v_toPure_1455_, lean_box(0), v_bestResult_x3f_1494_);
return v___x_1495_;
}
else
{
lean_object* v___x_1496_; uint8_t v___y_1498_; uint8_t v___y_1499_; uint8_t v___y_1508_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
lean_dec(v_bestResult_x3f_1494_);
v___x_1496_ = l_Lean_Elab_Info_stx(v_info_1457_);
v___x_1513_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__1));
lean_inc(v___x_1496_);
v___x_1514_ = l_Lean_Syntax_isOfKind(v___x_1496_, v___x_1513_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; 
lean_inc_ref(v_info_1457_);
v___x_1515_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_1457_);
if (lean_obj_tag(v___x_1515_) == 0)
{
v___y_1508_ = v___x_1514_;
goto v___jp_1507_;
}
else
{
lean_object* v_val_1516_; lean_object* v_elaborator_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
v_val_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_val_1516_);
lean_dec_ref_known(v___x_1515_, 1);
v_elaborator_1517_ = lean_ctor_get(v_val_1516_, 0);
lean_inc(v_elaborator_1517_);
lean_dec(v_val_1516_);
v___x_1518_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6));
v___x_1519_ = lean_name_eq(v_elaborator_1517_, v___x_1518_);
lean_dec(v_elaborator_1517_);
v___y_1508_ = v___x_1519_;
goto v___jp_1507_;
}
}
else
{
v___y_1508_ = v___x_1514_;
goto v___jp_1507_;
}
v___jp_1497_:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_Syntax_getRange_x3f(v___x_1496_, v___y_1498_);
lean_dec(v___x_1496_);
if (lean_obj_tag(v___x_1500_) == 1)
{
lean_object* v_val_1501_; uint8_t v___x_1502_; uint8_t v___x_1503_; 
v_val_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_val_1501_);
lean_dec_ref_known(v___x_1500_, 1);
v___x_1502_ = l_Lean_Syntax_Range_contains(v_val_1501_, v_hoverPos_1459_, v_includeStop_1460_);
v___x_1503_ = lean_bool_not(v___x_1502_);
if (v___x_1503_ == 0)
{
uint8_t v___x_1504_; 
v___x_1504_ = lean_bool_not(v___y_1499_);
v___y_1479_ = v___y_1498_;
v___y_1480_ = v_val_1501_;
v___y_1481_ = v___x_1504_;
goto v___jp_1478_;
}
else
{
v___y_1479_ = v___y_1498_;
v___y_1480_ = v_val_1501_;
v___y_1481_ = v___x_1503_;
goto v___jp_1478_;
}
}
else
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
lean_dec(v___x_1500_);
lean_dec_ref(v_children_1458_);
lean_dec_ref(v_info_1457_);
lean_dec_ref(v_ctx_1456_);
v___x_1505_ = lean_box(0);
v___x_1506_ = lean_apply_2(v_toPure_1455_, lean_box(0), v___x_1505_);
return v___x_1506_;
}
}
v___jp_1507_:
{
if (v___y_1508_ == 0)
{
uint8_t v___x_1509_; 
v___x_1509_ = 1;
switch(lean_obj_tag(v_info_1457_))
{
case 7:
{
v___y_1498_ = v___x_1509_;
v___y_1499_ = v___x_1509_;
goto v___jp_1497_;
}
case 5:
{
v___y_1498_ = v___x_1509_;
v___y_1499_ = v___x_1509_;
goto v___jp_1497_;
}
case 6:
{
v___y_1498_ = v___x_1509_;
v___y_1499_ = v___x_1509_;
goto v___jp_1497_;
}
default: 
{
lean_object* v___x_1510_; 
lean_inc_ref(v_info_1457_);
v___x_1510_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_1457_);
if (lean_obj_tag(v___x_1510_) == 0)
{
v___y_1498_ = v___x_1509_;
v___y_1499_ = v___y_1508_;
goto v___jp_1497_;
}
else
{
lean_dec_ref_known(v___x_1510_, 1);
v___y_1498_ = v___x_1509_;
v___y_1499_ = v___x_1509_;
goto v___jp_1497_;
}
}
}
}
else
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
lean_dec(v___x_1496_);
lean_dec_ref(v_children_1458_);
lean_dec_ref(v_info_1457_);
lean_dec_ref(v_ctx_1456_);
v___x_1511_ = lean_box(0);
v___x_1512_ = lean_apply_2(v_toPure_1455_, lean_box(0), v___x_1511_);
return v___x_1512_;
}
}
}
v___jp_1462_:
{
lean_object* v_priority_1467_; lean_object* v_result_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v_priority_1467_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_priority_1467_, 0, v___y_1464_);
lean_ctor_set_uint8(v_priority_1467_, sizeof(void*)*1, v___y_1465_);
lean_ctor_set_uint8(v_priority_1467_, sizeof(void*)*1 + 1, v___y_1463_);
lean_ctor_set_uint8(v_priority_1467_, sizeof(void*)*1 + 2, v___y_1466_);
v_result_1468_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_result_1468_, 0, v_ctx_1456_);
lean_ctor_set(v_result_1468_, 1, v_info_1457_);
lean_ctor_set(v_result_1468_, 2, v_children_1458_);
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v_priority_1467_);
lean_ctor_set(v___x_1469_, 1, v_result_1468_);
v___x_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
v___x_1471_ = lean_apply_2(v_toPure_1455_, lean_box(0), v___x_1470_);
return v___x_1471_;
}
v___jp_1472_:
{
if (lean_obj_tag(v_info_1457_) == 2)
{
v___y_1463_ = v___y_1477_;
v___y_1464_ = v___y_1475_;
v___y_1465_ = v___y_1476_;
v___y_1466_ = v___y_1473_;
goto v___jp_1462_;
}
else
{
v___y_1463_ = v___y_1477_;
v___y_1464_ = v___y_1475_;
v___y_1465_ = v___y_1476_;
v___y_1466_ = v___y_1474_;
goto v___jp_1462_;
}
}
v___jp_1478_:
{
if (v___y_1481_ == 0)
{
lean_object* v_start_1482_; lean_object* v_stop_1483_; uint8_t v___x_1484_; lean_object* v___x_1485_; 
v_start_1482_ = lean_ctor_get(v___y_1480_, 0);
lean_inc(v_start_1482_);
v_stop_1483_ = lean_ctor_get(v___y_1480_, 1);
lean_inc(v_stop_1483_);
lean_dec_ref(v___y_1480_);
v___x_1484_ = lean_nat_dec_eq(v_stop_1483_, v_hoverPos_1459_);
v___x_1485_ = lean_nat_sub(v_stop_1483_, v_start_1482_);
lean_dec(v_start_1482_);
lean_dec(v_stop_1483_);
if (lean_obj_tag(v_info_1457_) == 1)
{
lean_object* v_i_1486_; lean_object* v_expr_1487_; 
v_i_1486_ = lean_ctor_get(v_info_1457_, 0);
v_expr_1487_ = lean_ctor_get(v_i_1486_, 3);
if (lean_obj_tag(v_expr_1487_) == 1)
{
v___y_1473_ = v___y_1479_;
v___y_1474_ = v___y_1481_;
v___y_1475_ = v___x_1485_;
v___y_1476_ = v___x_1484_;
v___y_1477_ = v___y_1479_;
goto v___jp_1472_;
}
else
{
v___y_1473_ = v___y_1479_;
v___y_1474_ = v___y_1481_;
v___y_1475_ = v___x_1485_;
v___y_1476_ = v___x_1484_;
v___y_1477_ = v___y_1481_;
goto v___jp_1472_;
}
}
else
{
v___y_1473_ = v___y_1479_;
v___y_1474_ = v___y_1481_;
v___y_1475_ = v___x_1485_;
v___y_1476_ = v___x_1484_;
v___y_1477_ = v___y_1481_;
goto v___jp_1472_;
}
}
else
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_dec_ref(v___y_1480_);
lean_dec_ref(v_children_1458_);
lean_dec_ref(v_info_1457_);
lean_dec_ref(v_ctx_1456_);
v___x_1488_ = lean_box(0);
v___x_1489_ = lean_apply_2(v_toPure_1455_, lean_box(0), v___x_1488_);
return v___x_1489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___boxed(lean_object* v___f_1520_, lean_object* v___f_1521_, lean_object* v___x_1522_, lean_object* v_toPure_1523_, lean_object* v_ctx_1524_, lean_object* v_info_1525_, lean_object* v_children_1526_, lean_object* v_hoverPos_1527_, lean_object* v_includeStop_1528_, lean_object* v_results_1529_){
_start:
{
uint8_t v_includeStop_boxed_1530_; lean_object* v_res_1531_; 
v_includeStop_boxed_1530_ = lean_unbox(v_includeStop_1528_);
v_res_1531_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3(v___f_1520_, v___f_1521_, v___x_1522_, v_toPure_1523_, v_ctx_1524_, v_info_1525_, v_children_1526_, v_hoverPos_1527_, v_includeStop_boxed_1530_, v_results_1529_);
lean_dec(v_hoverPos_1527_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4(lean_object* v___f_1534_, lean_object* v___f_1535_, lean_object* v___x_1536_, lean_object* v_toPure_1537_, lean_object* v_hoverPos_1538_, uint8_t v_includeStop_1539_, lean_object* v___f_1540_, lean_object* v_filter_1541_, lean_object* v_toBind_1542_, lean_object* v_ctx_1543_, lean_object* v_info_1544_, lean_object* v_children_1545_, lean_object* v_results_1546_){
_start:
{
lean_object* v___x_1547_; lean_object* v___f_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1547_ = lean_box(v_includeStop_1539_);
lean_inc_ref(v_children_1545_);
lean_inc_ref(v_info_1544_);
lean_inc_ref(v_ctx_1543_);
v___f_1548_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_1548_, 0, v___f_1534_);
lean_closure_set(v___f_1548_, 1, v___f_1535_);
lean_closure_set(v___f_1548_, 2, v___x_1536_);
lean_closure_set(v___f_1548_, 3, v_toPure_1537_);
lean_closure_set(v___f_1548_, 4, v_ctx_1543_);
lean_closure_set(v___f_1548_, 5, v_info_1544_);
lean_closure_set(v___f_1548_, 6, v_children_1545_);
lean_closure_set(v___f_1548_, 7, v_hoverPos_1538_);
lean_closure_set(v___f_1548_, 8, v___x_1547_);
v___x_1549_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___closed__0));
v___x_1550_ = l_List_filterMapTR_go___redArg(v___f_1540_, v_results_1546_, v___x_1549_);
v___x_1551_ = lean_apply_4(v_filter_1541_, v_ctx_1543_, v_info_1544_, v_children_1545_, v___x_1550_);
v___x_1552_ = lean_apply_4(v_toBind_1542_, lean_box(0), lean_box(0), v___x_1551_, v___f_1548_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___boxed(lean_object* v___f_1553_, lean_object* v___f_1554_, lean_object* v___x_1555_, lean_object* v_toPure_1556_, lean_object* v_hoverPos_1557_, lean_object* v_includeStop_1558_, lean_object* v___f_1559_, lean_object* v_filter_1560_, lean_object* v_toBind_1561_, lean_object* v_ctx_1562_, lean_object* v_info_1563_, lean_object* v_children_1564_, lean_object* v_results_1565_){
_start:
{
uint8_t v_includeStop_boxed_1566_; lean_object* v_res_1567_; 
v_includeStop_boxed_1566_ = lean_unbox(v_includeStop_1558_);
v_res_1567_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4(v___f_1553_, v___f_1554_, v___x_1555_, v_toPure_1556_, v_hoverPos_1557_, v_includeStop_boxed_1566_, v___f_1559_, v_filter_1560_, v_toBind_1561_, v_ctx_1562_, v_info_1563_, v_children_1564_, v_results_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__6(lean_object* v_toPure_1568_, lean_object* v_results_1569_){
_start:
{
if (lean_obj_tag(v_results_1569_) == 0)
{
goto v___jp_1570_;
}
else
{
lean_object* v_val_1573_; 
v_val_1573_ = lean_ctor_get(v_results_1569_, 0);
lean_inc(v_val_1573_);
lean_dec_ref_known(v_results_1569_, 1);
if (lean_obj_tag(v_val_1573_) == 0)
{
goto v___jp_1570_;
}
else
{
lean_object* v_val_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1590_; 
v_val_1574_ = lean_ctor_get(v_val_1573_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_val_1573_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1576_ = v_val_1573_;
v_isShared_1577_ = v_isSharedCheck_1590_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_val_1574_);
lean_dec(v_val_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1590_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v_snd_1578_; lean_object* v_info_1579_; lean_object* v___x_1581_; 
v_snd_1578_ = lean_ctor_get(v_val_1574_, 1);
lean_inc(v_snd_1578_);
lean_dec(v_val_1574_);
v_info_1579_ = lean_ctor_get(v_snd_1578_, 1);
lean_inc_ref(v_info_1579_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v_snd_1578_);
v___x_1581_ = v___x_1576_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_snd_1578_);
v___x_1581_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
if (lean_obj_tag(v_info_1579_) == 1)
{
lean_object* v_i_1582_; lean_object* v_expr_1583_; uint8_t v___x_1584_; 
v_i_1582_ = lean_ctor_get(v_info_1579_, 0);
lean_inc_ref(v_i_1582_);
lean_dec_ref_known(v_info_1579_, 1);
v_expr_1583_ = lean_ctor_get(v_i_1582_, 3);
lean_inc_ref(v_expr_1583_);
lean_dec_ref(v_i_1582_);
v___x_1584_ = l_Lean_Expr_isSyntheticSorry(v_expr_1583_);
lean_dec_ref(v_expr_1583_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_apply_2(v_toPure_1568_, lean_box(0), v___x_1581_);
return v___x_1585_;
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
lean_dec_ref(v___x_1581_);
v___x_1586_ = lean_box(0);
v___x_1587_ = lean_apply_2(v_toPure_1568_, lean_box(0), v___x_1586_);
return v___x_1587_;
}
}
else
{
lean_object* v___x_1588_; 
lean_dec_ref(v_info_1579_);
v___x_1588_ = lean_apply_2(v_toPure_1568_, lean_box(0), v___x_1581_);
return v___x_1588_;
}
}
}
}
}
v___jp_1570_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = lean_box(0);
v___x_1572_ = lean_apply_2(v_toPure_1568_, lean_box(0), v___x_1571_);
return v___x_1572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg(lean_object* v_inst_1593_, lean_object* v_t_1594_, lean_object* v_hoverPos_1595_, uint8_t v_includeStop_1596_, lean_object* v_filter_1597_){
_start:
{
lean_object* v_toApplicative_1598_; lean_object* v_toBind_1599_; lean_object* v_toPure_1600_; lean_object* v___f_1601_; lean_object* v___f_1602_; lean_object* v___f_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v_postNode_1606_; lean_object* v___f_1607_; lean_object* v___f_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v_toApplicative_1598_ = lean_ctor_get(v_inst_1593_, 0);
v_toBind_1599_ = lean_ctor_get(v_inst_1593_, 1);
lean_inc_n(v_toBind_1599_, 2);
v_toPure_1600_ = lean_ctor_get(v_toApplicative_1598_, 1);
v___f_1601_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__0));
v___f_1602_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__1));
v___f_1603_ = ((lean_object*)(l_Lean_Elab_instMaxHoverableInfoPrio___closed__0));
v___x_1604_ = ((lean_object*)(l_Lean_Elab_instBEqHoverableInfoPrio___closed__0));
v___x_1605_ = lean_box(v_includeStop_1596_);
lean_inc_n(v_toPure_1600_, 3);
v_postNode_1606_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___boxed), 13, 9);
lean_closure_set(v_postNode_1606_, 0, v___f_1601_);
lean_closure_set(v_postNode_1606_, 1, v___f_1603_);
lean_closure_set(v_postNode_1606_, 2, v___x_1604_);
lean_closure_set(v_postNode_1606_, 3, v_toPure_1600_);
lean_closure_set(v_postNode_1606_, 4, v_hoverPos_1595_);
lean_closure_set(v_postNode_1606_, 5, v___x_1605_);
lean_closure_set(v_postNode_1606_, 6, v___f_1602_);
lean_closure_set(v_postNode_1606_, 7, v_filter_1597_);
lean_closure_set(v_postNode_1606_, 8, v_toBind_1599_);
v___f_1607_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__2___boxed), 4, 1);
lean_closure_set(v___f_1607_, 0, v_toPure_1600_);
v___f_1608_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__6), 2, 1);
lean_closure_set(v___f_1608_, 0, v_toPure_1600_);
v___x_1609_ = lean_box(0);
v___x_1610_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_1593_, v___f_1607_, v_postNode_1606_, v___x_1609_, v_t_1594_);
v___x_1611_ = lean_apply_4(v_toBind_1599_, lean_box(0), lean_box(0), v___x_1610_, v___f_1608_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___boxed(lean_object* v_inst_1612_, lean_object* v_t_1613_, lean_object* v_hoverPos_1614_, lean_object* v_includeStop_1615_, lean_object* v_filter_1616_){
_start:
{
uint8_t v_includeStop_boxed_1617_; lean_object* v_res_1618_; 
v_includeStop_boxed_1617_ = lean_unbox(v_includeStop_1615_);
v_res_1618_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg(v_inst_1612_, v_t_1613_, v_hoverPos_1614_, v_includeStop_boxed_1617_, v_filter_1616_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f(lean_object* v_m_1619_, lean_object* v_inst_1620_, lean_object* v_t_1621_, lean_object* v_hoverPos_1622_, uint8_t v_includeStop_1623_, lean_object* v_filter_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg(v_inst_1620_, v_t_1621_, v_hoverPos_1622_, v_includeStop_1623_, v_filter_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___boxed(lean_object* v_m_1626_, lean_object* v_inst_1627_, lean_object* v_t_1628_, lean_object* v_hoverPos_1629_, lean_object* v_includeStop_1630_, lean_object* v_filter_1631_){
_start:
{
uint8_t v_includeStop_boxed_1632_; lean_object* v_res_1633_; 
v_includeStop_boxed_1632_ = lean_unbox(v_includeStop_1630_);
v_res_1633_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f(v_m_1626_, v_inst_1627_, v_t_1628_, v_hoverPos_1629_, v_includeStop_boxed_1632_, v_filter_1631_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_type_x3f(lean_object* v_i_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
switch(lean_obj_tag(v_i_1634_))
{
case 1:
{
lean_object* v_i_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1665_; 
v_i_1640_ = lean_ctor_get(v_i_1634_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_i_1634_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1642_ = v_i_1634_;
v_isShared_1643_ = v_isSharedCheck_1665_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_i_1640_);
lean_dec(v_i_1634_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1665_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v_expr_1644_; lean_object* v___x_1645_; 
v_expr_1644_ = lean_ctor_get(v_i_1640_, 3);
lean_inc_ref(v_expr_1644_);
lean_dec_ref(v_i_1640_);
lean_inc(v_a_1638_);
lean_inc_ref(v_a_1637_);
lean_inc(v_a_1636_);
lean_inc_ref(v_a_1635_);
v___x_1645_ = lean_infer_type(v_expr_1644_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1656_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1648_ = v___x_1645_;
v_isShared_1649_ = v_isSharedCheck_1656_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1645_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1656_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v_a_1646_);
v___x_1651_ = v___x_1642_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1653_; 
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v___x_1651_);
v___x_1653_ = v___x_1648_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_del_object(v___x_1642_);
v_a_1657_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1645_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1645_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
}
case 7:
{
lean_object* v_i_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1691_; 
v_i_1666_ = lean_ctor_get(v_i_1634_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_i_1634_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1668_ = v_i_1634_;
v_isShared_1669_ = v_isSharedCheck_1691_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_i_1666_);
lean_dec(v_i_1634_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1691_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v_val_1670_; lean_object* v___x_1671_; 
v_val_1670_ = lean_ctor_get(v_i_1666_, 3);
lean_inc_ref(v_val_1670_);
lean_dec_ref(v_i_1666_);
lean_inc(v_a_1638_);
lean_inc_ref(v_a_1637_);
lean_inc(v_a_1636_);
lean_inc_ref(v_a_1635_);
v___x_1671_ = lean_infer_type(v_val_1670_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1682_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1674_ = v___x_1671_;
v_isShared_1675_ = v_isSharedCheck_1682_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1671_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1682_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1669_ == 0)
{
lean_ctor_set_tag(v___x_1668_, 1);
lean_ctor_set(v___x_1668_, 0, v_a_1672_);
v___x_1677_ = v___x_1668_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1679_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v___x_1677_);
v___x_1679_ = v___x_1674_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_del_object(v___x_1668_);
v_a_1683_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1671_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1671_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
case 13:
{
lean_object* v_i_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1718_; 
v_i_1692_ = lean_ctor_get(v_i_1634_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_i_1634_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1694_ = v_i_1634_;
v_isShared_1695_ = v_isSharedCheck_1718_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_i_1692_);
lean_dec(v_i_1634_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1718_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v_toTermInfo_1696_; lean_object* v_expr_1697_; lean_object* v___x_1698_; 
v_toTermInfo_1696_ = lean_ctor_get(v_i_1692_, 0);
lean_inc_ref(v_toTermInfo_1696_);
lean_dec_ref(v_i_1692_);
v_expr_1697_ = lean_ctor_get(v_toTermInfo_1696_, 3);
lean_inc_ref(v_expr_1697_);
lean_dec_ref(v_toTermInfo_1696_);
lean_inc(v_a_1638_);
lean_inc_ref(v_a_1637_);
lean_inc(v_a_1636_);
lean_inc_ref(v_a_1635_);
v___x_1698_ = lean_infer_type(v_expr_1697_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1709_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1701_ = v___x_1698_;
v_isShared_1702_ = v_isSharedCheck_1709_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1698_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1709_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1695_ == 0)
{
lean_ctor_set_tag(v___x_1694_, 1);
lean_ctor_set(v___x_1694_, 0, v_a_1699_);
v___x_1704_ = v___x_1694_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v___x_1706_; 
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1704_);
v___x_1706_ = v___x_1701_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_del_object(v___x_1694_);
v_a_1710_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1698_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1698_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
default: 
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
lean_dec_ref(v_i_1634_);
v___x_1719_ = lean_box(0);
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
return v___x_1720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_type_x3f___boxed(lean_object* v_i_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_Elab_Info_type_x3f(v_i_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
lean_dec(v_a_1725_);
lean_dec_ref(v_a_1724_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(lean_object* v_declName_1728_, uint8_t v_includeBuiltin_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v___x_1733_; lean_object* v_env_1734_; lean_object* v_ref_1735_; lean_object* v_currNamespace_1736_; lean_object* v_openDecls_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1733_ = lean_st_ref_get(v___y_1731_);
v_env_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc_ref(v_env_1734_);
lean_dec(v___x_1733_);
v_ref_1735_ = lean_ctor_get(v___y_1730_, 5);
v_currNamespace_1736_ = lean_ctor_get(v___y_1730_, 6);
v_openDecls_1737_ = lean_ctor_get(v___y_1730_, 7);
v___x_1738_ = l_Lean_Options_empty;
lean_inc(v_openDecls_1737_);
lean_inc(v_currNamespace_1736_);
v___x_1739_ = l_Lean_findDocString_x3f(v_env_1734_, v_declName_1728_, v_includeBuiltin_1729_, v___x_1738_, v_currNamespace_1736_, v_openDecls_1737_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1739_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1739_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1759_; 
v_a_1748_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1750_ = v___x_1739_;
v_isShared_1751_ = v_isSharedCheck_1759_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1739_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1759_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1752_ = lean_io_error_to_string(v_a_1748_);
v___x_1753_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
v___x_1754_ = l_Lean_MessageData_ofFormat(v___x_1753_);
lean_inc(v_ref_1735_);
v___x_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1755_, 0, v_ref_1735_);
lean_ctor_set(v___x_1755_, 1, v___x_1754_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v___x_1755_);
v___x_1757_ = v___x_1750_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg___boxed(lean_object* v_declName_1760_, lean_object* v_includeBuiltin_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
uint8_t v_includeBuiltin_boxed_1765_; lean_object* v_res_1766_; 
v_includeBuiltin_boxed_1765_ = lean_unbox(v_includeBuiltin_1761_);
v_res_1766_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_declName_1760_, v_includeBuiltin_boxed_1765_, v___y_1762_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0(lean_object* v_declName_1767_, uint8_t v_includeBuiltin_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_declName_1767_, v_includeBuiltin_1768_, v___y_1771_, v___y_1772_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___boxed(lean_object* v_declName_1775_, lean_object* v_includeBuiltin_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
uint8_t v_includeBuiltin_boxed_1782_; lean_object* v_res_1783_; 
v_includeBuiltin_boxed_1782_ = lean_unbox(v_includeBuiltin_1776_);
v_res_1783_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0(v_declName_1775_, v_includeBuiltin_boxed_1782_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg(lean_object* v_name_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v___x_1787_; lean_object* v_env_1788_; lean_object* v___x_1789_; lean_object* v_toEnvExtension_1790_; lean_object* v_asyncMode_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1787_ = lean_st_ref_get(v___y_1785_);
v_env_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc_ref(v_env_1788_);
lean_dec(v___x_1787_);
v___x_1789_ = l_Lean_errorExplanationExt;
v_toEnvExtension_1790_ = lean_ctor_get(v___x_1789_, 0);
v_asyncMode_1791_ = lean_ctor_get(v_toEnvExtension_1790_, 2);
v___x_1792_ = lean_box(1);
v___x_1793_ = lean_box(0);
v___x_1794_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1792_, v___x_1789_, v_env_1788_, v_asyncMode_1791_, v___x_1793_);
v___x_1795_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1794_, v_name_1784_);
lean_dec(v___x_1794_);
v___x_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg___boxed(lean_object* v_name_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg(v_name_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec(v_name_1797_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1(lean_object* v_name_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg(v_name_1801_, v___y_1805_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___boxed(lean_object* v_name_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1(v_name_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v_name_1808_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_docString_x3f(lean_object* v_i_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; 
switch(lean_obj_tag(v_i_1815_))
{
case 1:
{
lean_object* v_i_1837_; lean_object* v_expr_1838_; lean_object* v___x_1839_; 
v_i_1837_ = lean_ctor_get(v_i_1815_, 0);
v_expr_1838_ = lean_ctor_get(v_i_1837_, 3);
v___x_1839_ = l_Lean_Expr_constName_x3f(v_expr_1838_);
if (lean_obj_tag(v___x_1839_) == 1)
{
lean_object* v_val_1840_; uint8_t v___x_1841_; lean_object* v___x_1842_; 
lean_dec_ref_known(v_i_1815_, 1);
v_val_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_val_1840_);
lean_dec_ref_known(v___x_1839_, 1);
v___x_1841_ = 1;
v___x_1842_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_val_1840_, v___x_1841_, v_a_1818_, v_a_1819_);
return v___x_1842_;
}
else
{
lean_dec(v___x_1839_);
v___y_1822_ = v_a_1816_;
v___y_1823_ = v_a_1817_;
v___y_1824_ = v_a_1818_;
v___y_1825_ = v_a_1819_;
goto v___jp_1821_;
}
}
case 13:
{
lean_object* v_i_1843_; lean_object* v___x_1844_; 
v_i_1843_ = lean_ctor_get(v_i_1815_, 0);
v___x_1844_ = l_Lean_Meta_getPPContext(v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1846_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref_known(v___x_1844_, 1);
lean_inc_ref(v_i_1843_);
v___x_1846_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v_a_1845_, v_i_1843_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1860_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1860_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1860_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
if (lean_obj_tag(v_a_1847_) == 1)
{
lean_object* v___x_1852_; 
lean_dec_ref_known(v_i_1815_, 1);
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
else
{
lean_object* v_toTermInfo_1854_; lean_object* v_expr_1855_; lean_object* v___x_1856_; 
lean_del_object(v___x_1849_);
lean_dec(v_a_1847_);
v_toTermInfo_1854_ = lean_ctor_get(v_i_1843_, 0);
v_expr_1855_ = lean_ctor_get(v_toTermInfo_1854_, 3);
v___x_1856_ = l_Lean_Expr_constName_x3f(v_expr_1855_);
if (lean_obj_tag(v___x_1856_) == 1)
{
lean_object* v_val_1857_; uint8_t v___x_1858_; lean_object* v___x_1859_; 
lean_dec_ref_known(v_i_1815_, 1);
v_val_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_val_1857_);
lean_dec_ref_known(v___x_1856_, 1);
v___x_1858_ = 1;
v___x_1859_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_val_1857_, v___x_1858_, v_a_1818_, v_a_1819_);
return v___x_1859_;
}
else
{
lean_dec(v___x_1856_);
v___y_1822_ = v_a_1816_;
v___y_1823_ = v_a_1817_;
v___y_1824_ = v_a_1818_;
v___y_1825_ = v_a_1819_;
goto v___jp_1821_;
}
}
}
}
else
{
lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1879_; 
v_isSharedCheck_1879_ = !lean_is_exclusive(v_i_1815_);
if (v_isSharedCheck_1879_ == 0)
{
lean_object* v_unused_1880_; 
v_unused_1880_ = lean_ctor_get(v_i_1815_, 0);
lean_dec(v_unused_1880_);
v___x_1862_ = v_i_1815_;
v_isShared_1863_ = v_isSharedCheck_1879_;
goto v_resetjp_1861_;
}
else
{
lean_dec(v_i_1815_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1879_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1878_; 
v_a_1864_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1866_ = v___x_1846_;
v_isShared_1867_ = v_isSharedCheck_1878_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1846_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1878_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v_ref_1868_; lean_object* v___x_1869_; lean_object* v___x_1871_; 
v_ref_1868_ = lean_ctor_get(v_a_1818_, 5);
v___x_1869_ = lean_io_error_to_string(v_a_1864_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set_tag(v___x_1862_, 3);
lean_ctor_set(v___x_1862_, 0, v___x_1869_);
v___x_1871_ = v___x_1862_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1875_; 
v___x_1872_ = l_Lean_MessageData_ofFormat(v___x_1871_);
lean_inc(v_ref_1868_);
v___x_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1873_, 0, v_ref_1868_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 0, v___x_1873_);
v___x_1875_ = v___x_1866_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1873_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec_ref_known(v_i_1815_, 1);
v_a_1881_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1844_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1844_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
case 7:
{
lean_object* v_i_1889_; lean_object* v_projName_1890_; uint8_t v___x_1891_; lean_object* v___x_1892_; 
v_i_1889_ = lean_ctor_get(v_i_1815_, 0);
lean_inc_ref(v_i_1889_);
lean_dec_ref_known(v_i_1815_, 1);
v_projName_1890_ = lean_ctor_get(v_i_1889_, 0);
lean_inc(v_projName_1890_);
lean_dec_ref(v_i_1889_);
v___x_1891_ = 1;
v___x_1892_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_projName_1890_, v___x_1891_, v_a_1818_, v_a_1819_);
return v___x_1892_;
}
case 5:
{
lean_object* v_i_1893_; lean_object* v_optionName_1894_; lean_object* v_declName_1895_; uint8_t v___x_1896_; lean_object* v___x_1897_; 
v_i_1893_ = lean_ctor_get(v_i_1815_, 0);
lean_inc_ref(v_i_1893_);
lean_dec_ref_known(v_i_1815_, 1);
v_optionName_1894_ = lean_ctor_get(v_i_1893_, 1);
lean_inc(v_optionName_1894_);
v_declName_1895_ = lean_ctor_get(v_i_1893_, 2);
lean_inc(v_declName_1895_);
lean_dec_ref(v_i_1893_);
v___x_1896_ = 1;
v___x_1897_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_declName_1895_, v___x_1896_, v_a_1818_, v_a_1819_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
if (lean_obj_tag(v_a_1898_) == 1)
{
lean_dec_ref_known(v_a_1898_, 1);
lean_dec(v_optionName_1894_);
return v___x_1897_;
}
else
{
lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1940_; 
lean_dec(v_a_1898_);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1940_ == 0)
{
lean_object* v_unused_1941_; 
v_unused_1941_ = lean_ctor_get(v___x_1897_, 0);
lean_dec(v_unused_1941_);
v___x_1900_ = v___x_1897_;
v_isShared_1901_ = v_isSharedCheck_1940_;
goto v_resetjp_1899_;
}
else
{
lean_dec(v___x_1897_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1940_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1924_; 
lean_del_object(v___x_1900_);
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1905_ = v___x_1902_;
v_isShared_1906_ = v_isSharedCheck_1924_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1902_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1924_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1903_, v_optionName_1894_);
lean_dec(v_optionName_1894_);
lean_dec(v_a_1903_);
if (lean_obj_tag(v___x_1907_) == 1)
{
lean_object* v_val_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1919_; 
v_val_1908_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1910_ = v___x_1907_;
v_isShared_1911_ = v_isSharedCheck_1919_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_val_1908_);
lean_dec(v___x_1907_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1919_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1912_ = l_Lean_OptionDecl_fullDescr(v_val_1908_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v___x_1912_);
v___x_1914_ = v___x_1910_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1916_; 
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 0, v___x_1914_);
v___x_1916_ = v___x_1905_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1922_; 
lean_dec(v___x_1907_);
v___x_1920_ = lean_box(0);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 0, v___x_1920_);
v___x_1922_ = v___x_1905_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1920_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1939_; 
lean_dec(v_optionName_1894_);
v_a_1925_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1927_ = v___x_1902_;
v_isShared_1928_ = v_isSharedCheck_1939_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1902_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1939_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v_ref_1929_; lean_object* v___x_1930_; lean_object* v___x_1932_; 
v_ref_1929_ = lean_ctor_get(v_a_1818_, 5);
v___x_1930_ = lean_io_error_to_string(v_a_1925_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set_tag(v___x_1900_, 3);
lean_ctor_set(v___x_1900_, 0, v___x_1930_);
v___x_1932_ = v___x_1900_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1933_ = l_Lean_MessageData_ofFormat(v___x_1932_);
lean_inc(v_ref_1929_);
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v_ref_1929_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1934_);
v___x_1936_ = v___x_1927_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
}
}
}
else
{
lean_dec(v_optionName_1894_);
return v___x_1897_;
}
}
case 6:
{
lean_object* v_i_1942_; lean_object* v_errorName_1943_; lean_object* v___x_1944_; lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1965_; 
v_i_1942_ = lean_ctor_get(v_i_1815_, 0);
lean_inc_ref(v_i_1942_);
lean_dec_ref_known(v_i_1815_, 1);
v_errorName_1943_ = lean_ctor_get(v_i_1942_, 1);
lean_inc(v_errorName_1943_);
lean_dec_ref(v_i_1942_);
v___x_1944_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg(v_errorName_1943_, v_a_1819_);
lean_dec(v_errorName_1943_);
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1947_ = v___x_1944_;
v_isShared_1948_ = v_isSharedCheck_1965_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1944_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1965_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
if (lean_obj_tag(v_a_1945_) == 1)
{
lean_object* v_val_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1960_; 
v_val_1949_ = lean_ctor_get(v_a_1945_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_a_1945_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1951_ = v_a_1945_;
v_isShared_1952_ = v_isSharedCheck_1960_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_val_1949_);
lean_dec(v_a_1945_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1960_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1953_ = l_Lean_ErrorExplanation_summaryWithSeverity(v_val_1949_);
lean_dec(v_val_1949_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1953_);
v___x_1955_ = v___x_1951_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1953_);
v___x_1955_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1957_; 
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1955_);
v___x_1957_ = v___x_1947_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1963_; 
lean_dec(v_a_1945_);
v___x_1961_ = lean_box(0);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1961_);
v___x_1963_ = v___x_1947_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
case 15:
{
lean_object* v_i_1966_; lean_object* v_stx_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; lean_object* v___x_1970_; 
v_i_1966_ = lean_ctor_get(v_i_1815_, 0);
lean_inc_ref(v_i_1966_);
lean_dec_ref_known(v_i_1815_, 1);
v_stx_1967_ = lean_ctor_get(v_i_1966_, 1);
lean_inc(v_stx_1967_);
lean_dec_ref(v_i_1966_);
v___x_1968_ = l_Lean_Syntax_getKind(v_stx_1967_);
v___x_1969_ = 1;
v___x_1970_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v___x_1968_, v___x_1969_, v_a_1818_, v_a_1819_);
return v___x_1970_;
}
case 16:
{
lean_object* v_i_1971_; lean_object* v_name_1972_; uint8_t v___x_1973_; lean_object* v___x_1974_; 
v_i_1971_ = lean_ctor_get(v_i_1815_, 0);
lean_inc_ref(v_i_1971_);
lean_dec_ref_known(v_i_1815_, 1);
v_name_1972_ = lean_ctor_get(v_i_1971_, 1);
lean_inc(v_name_1972_);
lean_dec_ref(v_i_1971_);
v___x_1973_ = 1;
v___x_1974_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_name_1972_, v___x_1973_, v_a_1818_, v_a_1819_);
return v___x_1974_;
}
default: 
{
v___y_1822_ = v_a_1816_;
v___y_1823_ = v_a_1817_;
v___y_1824_ = v_a_1818_;
v___y_1825_ = v_a_1819_;
goto v___jp_1821_;
}
}
v___jp_1821_:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Lean_Elab_Info_toElabInfo_x3f(v_i_1815_);
if (lean_obj_tag(v___x_1826_) == 1)
{
lean_object* v_val_1827_; lean_object* v_elaborator_1828_; lean_object* v_stx_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; 
v_val_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_val_1827_);
lean_dec_ref_known(v___x_1826_, 1);
v_elaborator_1828_ = lean_ctor_get(v_val_1827_, 0);
lean_inc(v_elaborator_1828_);
v_stx_1829_ = lean_ctor_get(v_val_1827_, 1);
lean_inc(v_stx_1829_);
lean_dec(v_val_1827_);
v___x_1830_ = l_Lean_Syntax_getKind(v_stx_1829_);
v___x_1831_ = 1;
v___x_1832_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v___x_1830_, v___x_1831_, v___y_1824_, v___y_1825_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_a_1833_);
if (lean_obj_tag(v_a_1833_) == 0)
{
lean_object* v___x_1834_; 
lean_dec_ref_known(v___x_1832_, 1);
v___x_1834_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_elaborator_1828_, v___x_1831_, v___y_1824_, v___y_1825_);
return v___x_1834_;
}
else
{
lean_dec_ref_known(v_a_1833_, 1);
lean_dec(v_elaborator_1828_);
return v___x_1832_;
}
}
else
{
lean_dec(v_elaborator_1828_);
return v___x_1832_;
}
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_dec(v___x_1826_);
v___x_1835_ = lean_box(0);
v___x_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
return v___x_1836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_docString_x3f___boxed(lean_object* v_i_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_Elab_Info_docString_x3f(v_i_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
lean_dec(v_a_1977_);
lean_dec_ref(v_a_1976_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object* v_msgData_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v___x_1988_; lean_object* v_env_1989_; lean_object* v___x_1990_; lean_object* v_mctx_1991_; lean_object* v_lctx_1992_; lean_object* v_options_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1988_ = lean_st_ref_get(v___y_1986_);
v_env_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc_ref(v_env_1989_);
lean_dec(v___x_1988_);
v___x_1990_ = lean_st_ref_get(v___y_1984_);
v_mctx_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc_ref(v_mctx_1991_);
lean_dec(v___x_1990_);
v_lctx_1992_ = lean_ctor_get(v___y_1983_, 2);
v_options_1993_ = lean_ctor_get(v___y_1985_, 2);
lean_inc_ref(v_options_1993_);
lean_inc_ref(v_lctx_1992_);
v___x_1994_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1994_, 0, v_env_1989_);
lean_ctor_set(v___x_1994_, 1, v_mctx_1991_);
lean_ctor_set(v___x_1994_, 2, v_lctx_1992_);
lean_ctor_set(v___x_1994_, 3, v_options_1993_);
v___x_1995_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1994_);
lean_ctor_set(v___x_1995_, 1, v_msgData_1982_);
v___x_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v_ref_2010_; lean_object* v___x_2011_; lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2020_; 
v_ref_2010_ = lean_ctor_get(v___y_2007_, 5);
v___x_2011_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
lean_inc(v_ref_2010_);
v___x_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2016_, 0, v_ref_2010_);
lean_ctor_set(v___x_2016_, 1, v_a_2012_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set_tag(v___x_2014_, 1);
lean_ctor_set(v___x_2014_, 0, v___x_2016_);
v___x_2018_ = v___x_2014_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_2028_, lean_object* v_msg_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_fileName_2035_; lean_object* v_fileMap_2036_; lean_object* v_options_2037_; lean_object* v_currRecDepth_2038_; lean_object* v_maxRecDepth_2039_; lean_object* v_ref_2040_; lean_object* v_currNamespace_2041_; lean_object* v_openDecls_2042_; lean_object* v_initHeartbeats_2043_; lean_object* v_maxHeartbeats_2044_; lean_object* v_quotContext_2045_; lean_object* v_currMacroScope_2046_; uint8_t v_diag_2047_; lean_object* v_cancelTk_x3f_2048_; uint8_t v_suppressElabErrors_2049_; lean_object* v_inheritedTraceOptions_2050_; lean_object* v_ref_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v_fileName_2035_ = lean_ctor_get(v___y_2032_, 0);
v_fileMap_2036_ = lean_ctor_get(v___y_2032_, 1);
v_options_2037_ = lean_ctor_get(v___y_2032_, 2);
v_currRecDepth_2038_ = lean_ctor_get(v___y_2032_, 3);
v_maxRecDepth_2039_ = lean_ctor_get(v___y_2032_, 4);
v_ref_2040_ = lean_ctor_get(v___y_2032_, 5);
v_currNamespace_2041_ = lean_ctor_get(v___y_2032_, 6);
v_openDecls_2042_ = lean_ctor_get(v___y_2032_, 7);
v_initHeartbeats_2043_ = lean_ctor_get(v___y_2032_, 8);
v_maxHeartbeats_2044_ = lean_ctor_get(v___y_2032_, 9);
v_quotContext_2045_ = lean_ctor_get(v___y_2032_, 10);
v_currMacroScope_2046_ = lean_ctor_get(v___y_2032_, 11);
v_diag_2047_ = lean_ctor_get_uint8(v___y_2032_, sizeof(void*)*14);
v_cancelTk_x3f_2048_ = lean_ctor_get(v___y_2032_, 12);
v_suppressElabErrors_2049_ = lean_ctor_get_uint8(v___y_2032_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2050_ = lean_ctor_get(v___y_2032_, 13);
v_ref_2051_ = l_Lean_replaceRef(v_ref_2028_, v_ref_2040_);
lean_inc_ref(v_inheritedTraceOptions_2050_);
lean_inc(v_cancelTk_x3f_2048_);
lean_inc(v_currMacroScope_2046_);
lean_inc(v_quotContext_2045_);
lean_inc(v_maxHeartbeats_2044_);
lean_inc(v_initHeartbeats_2043_);
lean_inc(v_openDecls_2042_);
lean_inc(v_currNamespace_2041_);
lean_inc(v_maxRecDepth_2039_);
lean_inc(v_currRecDepth_2038_);
lean_inc_ref(v_options_2037_);
lean_inc_ref(v_fileMap_2036_);
lean_inc_ref(v_fileName_2035_);
v___x_2052_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2052_, 0, v_fileName_2035_);
lean_ctor_set(v___x_2052_, 1, v_fileMap_2036_);
lean_ctor_set(v___x_2052_, 2, v_options_2037_);
lean_ctor_set(v___x_2052_, 3, v_currRecDepth_2038_);
lean_ctor_set(v___x_2052_, 4, v_maxRecDepth_2039_);
lean_ctor_set(v___x_2052_, 5, v_ref_2051_);
lean_ctor_set(v___x_2052_, 6, v_currNamespace_2041_);
lean_ctor_set(v___x_2052_, 7, v_openDecls_2042_);
lean_ctor_set(v___x_2052_, 8, v_initHeartbeats_2043_);
lean_ctor_set(v___x_2052_, 9, v_maxHeartbeats_2044_);
lean_ctor_set(v___x_2052_, 10, v_quotContext_2045_);
lean_ctor_set(v___x_2052_, 11, v_currMacroScope_2046_);
lean_ctor_set(v___x_2052_, 12, v_cancelTk_x3f_2048_);
lean_ctor_set(v___x_2052_, 13, v_inheritedTraceOptions_2050_);
lean_ctor_set_uint8(v___x_2052_, sizeof(void*)*14, v_diag_2047_);
lean_ctor_set_uint8(v___x_2052_, sizeof(void*)*14 + 1, v_suppressElabErrors_2049_);
v___x_2053_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_2029_, v___y_2030_, v___y_2031_, v___x_2052_, v___y_2033_);
lean_dec_ref_known(v___x_2052_, 14);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_2054_, lean_object* v_msg_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_2054_, v_msg_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v_ref_2054_);
return v_res_2061_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2062_; 
v___x_2062_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2062_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
return v___x_2064_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2065_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_2066_ = lean_unsigned_to_nat(0u);
v___x_2067_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
lean_ctor_set(v___x_2067_, 2, v___x_2066_);
lean_ctor_set(v___x_2067_, 3, v___x_2066_);
lean_ctor_set(v___x_2067_, 4, v___x_2065_);
lean_ctor_set(v___x_2067_, 5, v___x_2065_);
lean_ctor_set(v___x_2067_, 6, v___x_2065_);
lean_ctor_set(v___x_2067_, 7, v___x_2065_);
lean_ctor_set(v___x_2067_, 8, v___x_2065_);
lean_ctor_set(v___x_2067_, 9, v___x_2065_);
return v___x_2067_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2068_ = lean_unsigned_to_nat(32u);
v___x_2069_ = lean_mk_empty_array_with_capacity(v___x_2068_);
v___x_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
return v___x_2070_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2071_ = ((size_t)5ULL);
v___x_2072_ = lean_unsigned_to_nat(0u);
v___x_2073_ = lean_unsigned_to_nat(32u);
v___x_2074_ = lean_mk_empty_array_with_capacity(v___x_2073_);
v___x_2075_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_2076_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
lean_ctor_set(v___x_2076_, 1, v___x_2074_);
lean_ctor_set(v___x_2076_, 2, v___x_2072_);
lean_ctor_set(v___x_2076_, 3, v___x_2072_);
lean_ctor_set_usize(v___x_2076_, 4, v___x_2071_);
return v___x_2076_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2077_ = lean_box(1);
v___x_2078_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_2079_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_2080_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
lean_ctor_set(v___x_2080_, 1, v___x_2078_);
lean_ctor_set(v___x_2080_, 2, v___x_2077_);
return v___x_2080_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_2083_ = l_Lean_stringToMessageData(v___x_2082_);
return v___x_2083_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_2086_ = l_Lean_stringToMessageData(v___x_2085_);
return v___x_2086_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_2089_ = l_Lean_stringToMessageData(v___x_2088_);
return v___x_2089_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_2092_ = l_Lean_stringToMessageData(v___x_2091_);
return v___x_2092_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2094_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_2095_ = l_Lean_stringToMessageData(v___x_2094_);
return v___x_2095_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_2098_ = l_Lean_stringToMessageData(v___x_2097_);
return v___x_2098_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_2101_ = l_Lean_stringToMessageData(v___x_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_2102_, lean_object* v_declHint_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v___x_2106_; lean_object* v_env_2107_; uint8_t v___y_2109_; uint8_t v___x_2165_; uint8_t v___x_2166_; 
v___x_2106_ = lean_st_ref_get(v___y_2104_);
v_env_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc_ref(v_env_2107_);
lean_dec(v___x_2106_);
v___x_2165_ = l_Lean_Name_isAnonymous(v_declHint_2103_);
v___x_2166_ = lean_bool_not(v___x_2165_);
if (v___x_2166_ == 0)
{
v___y_2109_ = v___x_2166_;
goto v___jp_2108_;
}
else
{
uint8_t v_isExporting_2167_; 
v_isExporting_2167_ = lean_ctor_get_uint8(v_env_2107_, sizeof(void*)*8);
v___y_2109_ = v_isExporting_2167_;
goto v___jp_2108_;
}
v___jp_2108_:
{
if (v___y_2109_ == 0)
{
lean_object* v___x_2110_; 
lean_dec_ref(v_env_2107_);
lean_dec(v_declHint_2103_);
v___x_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2110_, 0, v_msg_2102_);
return v___x_2110_;
}
else
{
uint8_t v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2111_ = 0;
lean_inc_ref(v_env_2107_);
v___x_2112_ = l_Lean_Environment_setExporting(v_env_2107_, v___x_2111_);
lean_inc(v_declHint_2103_);
lean_inc_ref(v___x_2112_);
v___x_2113_ = l_Lean_Environment_contains(v___x_2112_, v_declHint_2103_, v___y_2109_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; 
lean_dec_ref(v___x_2112_);
lean_dec_ref(v_env_2107_);
lean_dec(v_declHint_2103_);
v___x_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2114_, 0, v_msg_2102_);
return v___x_2114_;
}
else
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v_c_2120_; lean_object* v___x_2121_; 
v___x_2115_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_2116_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_2117_ = l_Lean_Options_empty;
v___x_2118_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2112_);
lean_ctor_set(v___x_2118_, 1, v___x_2115_);
lean_ctor_set(v___x_2118_, 2, v___x_2116_);
lean_ctor_set(v___x_2118_, 3, v___x_2117_);
lean_inc(v_declHint_2103_);
v___x_2119_ = l_Lean_MessageData_ofConstName(v_declHint_2103_, v___x_2111_);
v_c_2120_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2120_, 0, v___x_2118_);
lean_ctor_set(v_c_2120_, 1, v___x_2119_);
v___x_2121_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2107_, v_declHint_2103_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
lean_dec_ref(v_env_2107_);
lean_dec(v_declHint_2103_);
v___x_2122_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
lean_ctor_set(v___x_2123_, 1, v_c_2120_);
v___x_2124_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_2125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2123_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = l_Lean_MessageData_note(v___x_2125_);
v___x_2127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2127_, 0, v_msg_2102_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
return v___x_2128_;
}
else
{
lean_object* v_val_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2164_; 
v_val_2129_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2131_ = v___x_2121_;
v_isShared_2132_ = v_isSharedCheck_2164_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_val_2129_);
lean_dec(v___x_2121_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2164_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v_mod_2136_; uint8_t v___x_2137_; 
v___x_2133_ = lean_box(0);
v___x_2134_ = l_Lean_Environment_header(v_env_2107_);
lean_dec_ref(v_env_2107_);
v___x_2135_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2134_);
v_mod_2136_ = lean_array_get(v___x_2133_, v___x_2135_, v_val_2129_);
lean_dec(v_val_2129_);
lean_dec_ref(v___x_2135_);
v___x_2137_ = l_Lean_isPrivateName(v_declHint_2103_);
lean_dec(v_declHint_2103_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2149_; 
v___x_2138_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_2139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2138_);
lean_ctor_set(v___x_2139_, 1, v_c_2120_);
v___x_2140_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_2141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2139_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = l_Lean_MessageData_ofName(v_mod_2136_);
v___x_2143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2141_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_2145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = l_Lean_MessageData_note(v___x_2145_);
v___x_2147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2147_, 0, v_msg_2102_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set_tag(v___x_2131_, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2147_);
v___x_2149_ = v___x_2131_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2147_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
else
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2151_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
lean_ctor_set(v___x_2152_, 1, v_c_2120_);
v___x_2153_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_2154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2152_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = l_Lean_MessageData_ofName(v_mod_2136_);
v___x_2156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2154_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_2158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2156_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = l_Lean_MessageData_note(v___x_2158_);
v___x_2160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2160_, 0, v_msg_2102_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set_tag(v___x_2131_, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2160_);
v___x_2162_ = v___x_2131_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_2168_, lean_object* v_declHint_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_2168_, v_declHint_2169_, v___y_2170_);
lean_dec(v___y_2170_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_2173_, lean_object* v_declHint_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v___x_2180_; lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2190_; 
v___x_2180_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_2173_, v_declHint_2174_, v___y_2178_);
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2183_ = v___x_2180_;
v_isShared_2184_ = v_isSharedCheck_2190_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2180_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2190_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2188_; 
v___x_2185_ = l_Lean_unknownIdentifierMessageTag;
v___x_2186_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
lean_ctor_set(v___x_2186_, 1, v_a_2181_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v___x_2186_);
v___x_2188_ = v___x_2183_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2186_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_2191_, lean_object* v_declHint_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2191_, v_declHint_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_2199_, lean_object* v_msg_2200_, lean_object* v_declHint_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v___x_2207_; lean_object* v_a_2208_; lean_object* v___x_2209_; 
v___x_2207_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2200_, v_declHint_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2208_);
lean_dec_ref(v___x_2207_);
v___x_2209_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_2199_, v_a_2208_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_2210_, lean_object* v_msg_2211_, lean_object* v_declHint_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_2210_, v_msg_2211_, v_declHint_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v_ref_2210_);
return v_res_2218_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_2221_ = l_Lean_stringToMessageData(v___x_2220_);
return v___x_2221_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2));
v___x_2224_ = l_Lean_stringToMessageData(v___x_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_2225_, lean_object* v_constName_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v___x_2232_; uint8_t v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2232_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_2233_ = 0;
lean_inc(v_constName_2226_);
v___x_2234_ = l_Lean_MessageData_ofConstName(v_constName_2226_, v___x_2233_);
v___x_2235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2232_);
lean_ctor_set(v___x_2235_, 1, v___x_2234_);
v___x_2236_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_2237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2235_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
v___x_2238_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_2225_, v___x_2237_, v_constName_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_2239_, lean_object* v_constName_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2239_, v_constName_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v_ref_2239_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v_ref_2253_; lean_object* v___x_2254_; 
v_ref_2253_ = lean_ctor_get(v___y_2250_, 5);
v___x_2254_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2253_, v_constName_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(lean_object* v_constName_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2268_; lean_object* v_env_2269_; uint8_t v___x_2270_; lean_object* v___x_2271_; 
v___x_2268_ = lean_st_ref_get(v___y_2266_);
v_env_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc_ref(v_env_2269_);
lean_dec(v___x_2268_);
v___x_2270_ = 0;
lean_inc(v_constName_2262_);
v___x_2271_ = l_Lean_Environment_find_x3f(v_env_2269_, v_constName_2262_, v___x_2270_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v___x_2272_; 
v___x_2272_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
return v___x_2272_;
}
else
{
lean_object* v_val_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec(v_constName_2262_);
v_val_2273_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2271_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_val_2273_);
lean_dec(v___x_2271_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
lean_ctor_set_tag(v___x_2275_, 0);
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_val_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0___boxed(lean_object* v_constName_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(v_constName_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(lean_object* v_declName_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v___x_2294_; 
lean_inc(v_declName_2288_);
v___x_2294_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(v_declName_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2321_; 
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2321_ == 0)
{
lean_object* v_unused_2322_; 
v_unused_2322_ = lean_ctor_get(v___x_2294_, 0);
lean_dec(v_unused_2322_);
v___x_2296_ = v___x_2294_;
v_isShared_2297_ = v_isSharedCheck_2321_;
goto v_resetjp_2295_;
}
else
{
lean_dec(v___x_2294_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2321_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v_env_2299_; lean_object* v___x_2300_; 
v___x_2298_ = lean_st_ref_get(v___y_2292_);
v_env_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc_ref(v_env_2299_);
lean_dec(v___x_2298_);
v___x_2300_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2299_, v_declName_2288_);
lean_dec(v_declName_2288_);
lean_dec_ref(v_env_2299_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v___x_2301_; lean_object* v___x_2303_; 
v___x_2301_ = lean_box(0);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2301_);
v___x_2303_ = v___x_2296_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v___x_2301_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
else
{
lean_object* v_val_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2320_; 
v_val_2305_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2307_ = v___x_2300_;
v_isShared_2308_ = v_isSharedCheck_2320_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_val_2305_);
lean_dec(v___x_2300_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2320_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2309_; lean_object* v_env_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2315_; 
v___x_2309_ = lean_st_ref_get(v___y_2292_);
v_env_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc_ref(v_env_2310_);
lean_dec(v___x_2309_);
v___x_2311_ = lean_box(0);
v___x_2312_ = l_Lean_Environment_allImportedModuleNames(v_env_2310_);
lean_dec_ref(v_env_2310_);
v___x_2313_ = lean_array_get(v___x_2311_, v___x_2312_, v_val_2305_);
lean_dec(v_val_2305_);
lean_dec_ref(v___x_2312_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v___x_2313_);
v___x_2315_ = v___x_2307_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
lean_object* v___x_2317_; 
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2315_);
v___x_2317_ = v___x_2296_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2315_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_dec(v_declName_2288_);
v_a_2323_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2294_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2294_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0___boxed(lean_object* v_declName_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(v_declName_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(lean_object* v_decl_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(v_decl_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2377_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2353_ = v___x_2350_;
v_isShared_2354_ = v_isSharedCheck_2377_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2377_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
if (lean_obj_tag(v_a_2351_) == 1)
{
lean_object* v_val_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2372_; 
v_val_2355_ = lean_ctor_get(v_a_2351_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_a_2351_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2357_ = v_a_2351_;
v_isShared_2358_ = v_isSharedCheck_2372_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_val_2355_);
lean_dec(v_a_2351_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2372_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2359_; uint8_t v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2367_; 
v___x_2359_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__1));
v___x_2360_ = 1;
v___x_2361_ = l_Lean_Name_toString(v_val_2355_, v___x_2360_);
v___x_2362_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
v___x_2363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2359_);
lean_ctor_set(v___x_2363_, 1, v___x_2362_);
v___x_2364_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__3));
v___x_2365_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2363_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v___x_2365_);
v___x_2367_ = v___x_2357_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2369_; 
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2367_);
v___x_2369_ = v___x_2353_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
else
{
lean_object* v___x_2373_; lean_object* v___x_2375_; 
lean_dec(v_a_2351_);
v___x_2373_ = lean_box(0);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2373_);
v___x_2375_ = v___x_2353_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2373_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
v_a_2378_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2350_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2350_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2381_ == 0)
{
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2378_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___boxed(lean_object* v_decl_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(v_decl_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2393_, lean_object* v_constName_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2401_, lean_object* v_constName_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1(v_00_u03b1_2401_, v_constName_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2409_, lean_object* v_ref_2410_, lean_object* v_constName_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2410_, v_constName_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2418_, lean_object* v_ref_2419_, lean_object* v_constName_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2418_, v_ref_2419_, v_constName_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v_ref_2419_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_2427_, lean_object* v_ref_2428_, lean_object* v_msg_2429_, lean_object* v_declHint_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_2428_, v_msg_2429_, v_declHint_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2437_, lean_object* v_ref_2438_, lean_object* v_msg_2439_, lean_object* v_declHint_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_00_u03b1_2437_, v_ref_2438_, v_msg_2439_, v_declHint_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v_ref_2438_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_2447_, lean_object* v_declHint_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_2447_, v_declHint_2448_, v___y_2452_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2455_, lean_object* v_declHint_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_2455_, v_declHint_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_2463_, lean_object* v_ref_2464_, lean_object* v_msg_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_2464_, v_msg_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2472_, lean_object* v_ref_2473_, lean_object* v_msg_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_2472_, v_ref_2473_, v_msg_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v_ref_2473_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_2481_, lean_object* v_msg_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v___x_2488_; 
v___x_2488_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2489_, lean_object* v_msg_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_2489_, v_msg_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
return v_res_2496_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(lean_object* v_a_2497_){
_start:
{
switch(lean_obj_tag(v_a_2497_))
{
case 3:
{
uint8_t v___x_2498_; 
v___x_2498_ = 1;
return v___x_2498_;
}
case 6:
{
lean_object* v_a_2499_; 
v_a_2499_ = lean_ctor_get(v_a_2497_, 0);
v_a_2497_ = v_a_2499_;
goto _start;
}
case 4:
{
lean_object* v_f_2501_; 
v_f_2501_ = lean_ctor_get(v_a_2497_, 1);
v_a_2497_ = v_f_2501_;
goto _start;
}
case 7:
{
lean_object* v_a_2503_; 
v_a_2503_ = lean_ctor_get(v_a_2497_, 1);
v_a_2497_ = v_a_2503_;
goto _start;
}
default: 
{
uint8_t v___x_2505_; 
v___x_2505_ = 0;
return v___x_2505_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat___boxed(lean_object* v_a_2506_){
_start:
{
uint8_t v_res_2507_; lean_object* v_r_2508_; 
v_res_2507_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(v_a_2506_);
lean_dec(v_a_2506_);
v_r_2508_ = lean_box(v_res_2507_);
return v_r_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(lean_object* v_e_2509_, lean_object* v___y_2510_){
_start:
{
uint8_t v___x_2512_; uint8_t v___x_2513_; 
v___x_2512_ = l_Lean_Expr_hasMVar(v_e_2509_);
v___x_2513_ = lean_bool_not(v___x_2512_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2514_; lean_object* v_mctx_2515_; lean_object* v___x_2516_; lean_object* v_fst_2517_; lean_object* v_snd_2518_; lean_object* v___x_2519_; lean_object* v_cache_2520_; lean_object* v_zetaDeltaFVarIds_2521_; lean_object* v_postponed_2522_; lean_object* v_diag_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2532_; 
v___x_2514_ = lean_st_ref_get(v___y_2510_);
v_mctx_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc_ref(v_mctx_2515_);
lean_dec(v___x_2514_);
v___x_2516_ = l_Lean_instantiateMVarsCore(v_mctx_2515_, v_e_2509_);
v_fst_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_fst_2517_);
v_snd_2518_ = lean_ctor_get(v___x_2516_, 1);
lean_inc(v_snd_2518_);
lean_dec_ref(v___x_2516_);
v___x_2519_ = lean_st_ref_take(v___y_2510_);
v_cache_2520_ = lean_ctor_get(v___x_2519_, 1);
v_zetaDeltaFVarIds_2521_ = lean_ctor_get(v___x_2519_, 2);
v_postponed_2522_ = lean_ctor_get(v___x_2519_, 3);
v_diag_2523_ = lean_ctor_get(v___x_2519_, 4);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; 
v_unused_2533_ = lean_ctor_get(v___x_2519_, 0);
lean_dec(v_unused_2533_);
v___x_2525_ = v___x_2519_;
v_isShared_2526_ = v_isSharedCheck_2532_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_diag_2523_);
lean_inc(v_postponed_2522_);
lean_inc(v_zetaDeltaFVarIds_2521_);
lean_inc(v_cache_2520_);
lean_dec(v___x_2519_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2532_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v_snd_2518_);
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_snd_2518_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_cache_2520_);
lean_ctor_set(v_reuseFailAlloc_2531_, 2, v_zetaDeltaFVarIds_2521_);
lean_ctor_set(v_reuseFailAlloc_2531_, 3, v_postponed_2522_);
lean_ctor_set(v_reuseFailAlloc_2531_, 4, v_diag_2523_);
v___x_2528_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = lean_st_ref_set(v___y_2510_, v___x_2528_);
v___x_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2530_, 0, v_fst_2517_);
return v___x_2530_;
}
}
}
else
{
lean_object* v___x_2534_; 
v___x_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2534_, 0, v_e_2509_);
return v___x_2534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg___boxed(lean_object* v_e_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_e_2535_, v___y_2536_);
lean_dec(v___y_2536_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0(lean_object* v_e_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_e_2539_, v___y_2541_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___boxed(lean_object* v_e_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0(v_e_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(lean_object* v_i_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
switch(lean_obj_tag(v_i_2564_))
{
case 1:
{
lean_object* v_i_2570_; lean_object* v_expr_2571_; uint8_t v_isDisplayableTerm_2572_; lean_object* v___x_2573_; lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2697_; 
v_i_2570_ = lean_ctor_get(v_i_2564_, 0);
lean_inc_ref(v_i_2570_);
lean_dec_ref_known(v_i_2564_, 1);
v_expr_2571_ = lean_ctor_get(v_i_2570_, 3);
lean_inc_ref(v_expr_2571_);
v_isDisplayableTerm_2572_ = lean_ctor_get_uint8(v_i_2570_, sizeof(void*)*4 + 1);
lean_dec_ref(v_i_2570_);
v___x_2573_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_expr_2571_, v_a_2566_);
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2576_ = v___x_2573_;
v_isShared_2577_ = v_isSharedCheck_2697_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2573_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2697_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
uint8_t v___x_2578_; 
v___x_2578_ = l_Lean_Expr_isSort(v_a_2574_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; 
lean_del_object(v___x_2576_);
lean_inc(v_a_2568_);
lean_inc_ref(v_a_2567_);
lean_inc(v_a_2566_);
lean_inc_ref(v_a_2565_);
lean_inc(v_a_2574_);
v___x_2579_ = lean_infer_type(v_a_2574_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v___x_2581_; lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2684_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref_known(v___x_2579_, 1);
v___x_2581_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_a_2580_, v_a_2566_);
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2584_ = v___x_2581_;
v_isShared_2585_ = v_isSharedCheck_2684_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2581_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2684_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Lean_Meta_ppExpr(v_a_2582_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
if (lean_obj_tag(v___x_2586_) == 0)
{
if (lean_obj_tag(v_a_2574_) == 4)
{
lean_object* v_declName_2587_; lean_object* v___x_2588_; 
lean_dec_ref_known(v___x_2586_, 1);
v_declName_2587_ = lean_ctor_get(v_a_2574_, 0);
lean_inc_n(v_declName_2587_, 2);
lean_dec_ref_known(v_a_2574_, 2);
v___x_2588_ = l_Lean_PrettyPrinter_ppSignature(v_declName_2587_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2590_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v___x_2588_, 1);
v___x_2590_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(v_declName_2587_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2615_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2593_ = v___x_2590_;
v_isShared_2594_ = v_isSharedCheck_2615_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2590_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2615_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v_fmt_2595_; lean_object* v_infos_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2614_; 
v_fmt_2595_ = lean_ctor_get(v_a_2589_, 0);
v_infos_2596_ = lean_ctor_get(v_a_2589_, 1);
v_isSharedCheck_2614_ = !lean_is_exclusive(v_a_2589_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2598_ = v_a_2589_;
v_isShared_2599_ = v_isSharedCheck_2614_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_infos_2596_);
lean_inc(v_fmt_2595_);
lean_dec(v_a_2589_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2614_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2605_; 
v___x_2600_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1));
v___x_2601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
lean_ctor_set(v___x_2601_, 1, v_fmt_2595_);
v___x_2602_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3));
v___x_2603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2601_);
lean_ctor_set(v___x_2603_, 1, v___x_2602_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2603_);
v___x_2605_ = v___x_2598_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2603_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v_infos_2596_);
v___x_2605_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
lean_object* v___x_2607_; 
if (v_isShared_2585_ == 0)
{
lean_ctor_set_tag(v___x_2584_, 1);
lean_ctor_set(v___x_2584_, 0, v___x_2605_);
v___x_2607_ = v___x_2584_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
lean_object* v___x_2608_; lean_object* v___x_2610_; 
v___x_2608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
lean_ctor_set(v___x_2608_, 1, v_a_2591_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2608_);
v___x_2610_ = v___x_2593_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
}
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec(v_a_2589_);
lean_del_object(v___x_2584_);
v_a_2616_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2590_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2590_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec(v_declName_2587_);
lean_del_object(v___x_2584_);
v_a_2624_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2588_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2588_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2633_; 
v_a_2632_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2632_);
lean_dec_ref_known(v___x_2586_, 1);
lean_inc(v_a_2574_);
v___x_2633_ = l_Lean_Meta_ppExpr(v_a_2574_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2667_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2636_ = v___x_2633_;
v_isShared_2637_ = v_isSharedCheck_2667_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2633_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2667_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___y_2639_; uint8_t v___y_2659_; 
if (v_isDisplayableTerm_2572_ == 0)
{
if (lean_obj_tag(v_a_2574_) == 1)
{
lean_object* v_lctx_2660_; lean_object* v___x_2661_; 
v_lctx_2660_ = lean_ctor_get(v_a_2565_, 2);
lean_inc_ref(v_lctx_2660_);
v___x_2661_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_2660_, v_a_2574_);
lean_dec_ref_known(v_a_2574_, 1);
if (lean_obj_tag(v___x_2661_) == 1)
{
lean_object* v_val_2662_; lean_object* v___x_2663_; uint8_t v___x_2664_; uint8_t v___x_2665_; 
v_val_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_val_2662_);
lean_dec_ref_known(v___x_2661_, 1);
v___x_2663_ = l_Lean_LocalDecl_userName(v_val_2662_);
lean_dec(v_val_2662_);
v___x_2664_ = l_Lean_Name_hasMacroScopes(v___x_2663_);
lean_dec(v___x_2663_);
v___x_2665_ = lean_bool_not(v___x_2664_);
v___y_2659_ = v___x_2665_;
goto v___jp_2658_;
}
else
{
lean_dec(v___x_2661_);
v___y_2659_ = v___x_2578_;
goto v___jp_2658_;
}
}
else
{
uint8_t v___x_2666_; 
lean_dec(v_a_2574_);
v___x_2666_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(v_a_2634_);
v___y_2659_ = v___x_2666_;
goto v___jp_2658_;
}
}
else
{
lean_dec(v_a_2574_);
goto v___jp_2654_;
}
v___jp_2638_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2647_; 
v___x_2640_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1));
v___x_2641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2640_);
lean_ctor_set(v___x_2641_, 1, v___y_2639_);
v___x_2642_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3));
v___x_2643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2641_);
lean_ctor_set(v___x_2643_, 1, v___x_2642_);
v___x_2644_ = lean_box(1);
v___x_2645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2643_);
lean_ctor_set(v___x_2645_, 1, v___x_2644_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set_tag(v___x_2584_, 1);
lean_ctor_set(v___x_2584_, 0, v___x_2645_);
v___x_2647_ = v___x_2584_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2648_ = lean_box(0);
v___x_2649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2647_);
lean_ctor_set(v___x_2649_, 1, v___x_2648_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 0, v___x_2649_);
v___x_2651_ = v___x_2636_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
v___jp_2654_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2655_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5));
v___x_2656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2656_, 0, v_a_2634_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
v___x_2657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2656_);
lean_ctor_set(v___x_2657_, 1, v_a_2632_);
v___y_2639_ = v___x_2657_;
goto v___jp_2638_;
}
v___jp_2658_:
{
if (v___y_2659_ == 0)
{
lean_dec(v_a_2634_);
v___y_2639_ = v_a_2632_;
goto v___jp_2638_;
}
else
{
goto v___jp_2654_;
}
}
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec(v_a_2632_);
lean_del_object(v___x_2584_);
lean_dec(v_a_2574_);
v_a_2668_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2633_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2633_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_del_object(v___x_2584_);
lean_dec(v_a_2574_);
v_a_2676_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2586_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2586_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec(v_a_2574_);
v_a_2685_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2579_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2579_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
else
{
lean_object* v___x_2693_; lean_object* v___x_2695_; 
lean_dec(v_a_2574_);
v___x_2693_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6));
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v___x_2693_);
v___x_2695_ = v___x_2576_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
case 7:
{
lean_object* v_i_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2748_; 
v_i_2698_ = lean_ctor_get(v_i_2564_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v_i_2564_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2700_ = v_i_2564_;
v_isShared_2701_ = v_isSharedCheck_2748_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_i_2698_);
lean_dec(v_i_2564_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2748_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v_fieldName_2702_; lean_object* v_val_2703_; lean_object* v___x_2704_; 
v_fieldName_2702_ = lean_ctor_get(v_i_2698_, 1);
lean_inc(v_fieldName_2702_);
v_val_2703_ = lean_ctor_get(v_i_2698_, 3);
lean_inc_ref(v_val_2703_);
lean_dec_ref(v_i_2698_);
lean_inc(v_a_2568_);
lean_inc_ref(v_a_2567_);
lean_inc(v_a_2566_);
lean_inc_ref(v_a_2565_);
v___x_2704_ = lean_infer_type(v_val_2703_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; lean_object* v___x_2706_; 
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2704_, 1);
v___x_2706_ = l_Lean_Meta_ppExpr(v_a_2705_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2731_; 
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2709_ = v___x_2706_;
v_isShared_2710_ = v_isSharedCheck_2731_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2706_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2731_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2711_; uint8_t v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2715_; 
v___x_2711_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1));
v___x_2712_ = 1;
v___x_2713_ = l_Lean_Name_toString(v_fieldName_2702_, v___x_2712_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set_tag(v___x_2700_, 3);
lean_ctor_set(v___x_2700_, 0, v___x_2713_);
v___x_2715_ = v___x_2700_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2713_);
v___x_2715_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2728_; 
v___x_2716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2711_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
v___x_2717_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5));
v___x_2718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2716_);
lean_ctor_set(v___x_2718_, 1, v___x_2717_);
v___x_2719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
lean_ctor_set(v___x_2719_, 1, v_a_2707_);
v___x_2720_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3));
v___x_2721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2719_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = lean_box(1);
v___x_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2721_);
lean_ctor_set(v___x_2723_, 1, v___x_2722_);
v___x_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
v___x_2725_ = lean_box(0);
v___x_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2724_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 0, v___x_2726_);
v___x_2728_ = v___x_2709_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2726_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
else
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2739_; 
lean_dec(v_fieldName_2702_);
lean_del_object(v___x_2700_);
v_a_2732_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2734_ = v___x_2706_;
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2706_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
else
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
lean_dec(v_fieldName_2702_);
lean_del_object(v___x_2700_);
v_a_2740_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2704_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2704_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
}
default: 
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
lean_dec_ref(v_i_2564_);
v___x_2749_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6));
v___x_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2749_);
return v___x_2750_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___boxed(lean_object* v_i_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(v_i_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_);
lean_dec(v_a_2755_);
lean_dec_ref(v_a_2754_);
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__0(lean_object* v_snd_2758_, lean_object* v_____r_2759_, lean_object* v_fmts_2760_, lean_object* v_infos_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2767_, 0, v_fmts_2760_);
lean_ctor_set(v___x_2767_, 1, v_infos_2761_);
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v_snd_2758_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
v___x_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2768_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__0___boxed(lean_object* v_snd_2770_, lean_object* v_____r_2771_, lean_object* v_fmts_2772_, lean_object* v_infos_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(v_snd_2770_, v_____r_2771_, v_fmts_2772_, v_infos_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0_spec__0(lean_object* v_x_2780_, lean_object* v_x_2781_, lean_object* v_x_2782_){
_start:
{
if (lean_obj_tag(v_x_2782_) == 0)
{
lean_dec(v_x_2780_);
return v_x_2781_;
}
else
{
lean_object* v_head_2783_; lean_object* v_tail_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2793_; 
v_head_2783_ = lean_ctor_get(v_x_2782_, 0);
v_tail_2784_ = lean_ctor_get(v_x_2782_, 1);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_x_2782_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2786_ = v_x_2782_;
v_isShared_2787_ = v_isSharedCheck_2793_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_tail_2784_);
lean_inc(v_head_2783_);
lean_dec(v_x_2782_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2793_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
lean_inc(v_x_2780_);
if (v_isShared_2787_ == 0)
{
lean_ctor_set_tag(v___x_2786_, 5);
lean_ctor_set(v___x_2786_, 1, v_x_2780_);
lean_ctor_set(v___x_2786_, 0, v_x_2781_);
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_x_2781_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v_x_2780_);
v___x_2789_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
lean_object* v___x_2790_; 
v___x_2790_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
lean_ctor_set(v___x_2790_, 1, v_head_2783_);
v_x_2781_ = v___x_2790_;
v_x_2782_ = v_tail_2784_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0(lean_object* v_x_2794_, lean_object* v_x_2795_){
_start:
{
if (lean_obj_tag(v_x_2794_) == 0)
{
lean_object* v___x_2796_; 
lean_dec(v_x_2795_);
v___x_2796_ = lean_box(0);
return v___x_2796_;
}
else
{
lean_object* v_tail_2797_; 
v_tail_2797_ = lean_ctor_get(v_x_2794_, 1);
if (lean_obj_tag(v_tail_2797_) == 0)
{
lean_object* v_head_2798_; 
lean_dec(v_x_2795_);
v_head_2798_ = lean_ctor_get(v_x_2794_, 0);
lean_inc(v_head_2798_);
lean_dec_ref_known(v_x_2794_, 2);
return v_head_2798_;
}
else
{
lean_object* v_head_2799_; lean_object* v___x_2800_; 
lean_inc(v_tail_2797_);
v_head_2799_ = lean_ctor_get(v_x_2794_, 0);
lean_inc(v_head_2799_);
lean_dec_ref_known(v_x_2794_, 2);
v___x_2800_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0_spec__0(v_x_2795_, v_head_2799_, v_tail_2797_);
return v___x_2800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__1(lean_object* v___x_2804_, lean_object* v_i_2805_, lean_object* v_fmts_2806_, lean_object* v_infos_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
lean_object* v___y_2814_; lean_object* v_fmts_2815_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v_fmts_2829_; lean_object* v_a_2833_; lean_object* v___y_2861_; uint8_t v___y_2862_; lean_object* v_a_2868_; lean_object* v___y_2872_; lean_object* v___x_2874_; 
lean_inc_ref(v_i_2805_);
v___x_2874_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(v_i_2805_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v_fst_2876_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
v_fst_2876_ = lean_ctor_get(v_a_2875_, 0);
if (lean_obj_tag(v_fst_2876_) == 1)
{
lean_object* v_val_2877_; lean_object* v_snd_2878_; lean_object* v_fmt_2879_; lean_object* v_infos_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
lean_dec(v_infos_2807_);
v_val_2877_ = lean_ctor_get(v_fst_2876_, 0);
lean_inc(v_val_2877_);
v_snd_2878_ = lean_ctor_get(v_a_2875_, 1);
lean_inc(v_snd_2878_);
lean_dec(v_a_2875_);
v_fmt_2879_ = lean_ctor_get(v_val_2877_, 0);
lean_inc(v_fmt_2879_);
v_infos_2880_ = lean_ctor_get(v_val_2877_, 1);
lean_inc(v_infos_2880_);
lean_dec(v_val_2877_);
v___x_2881_ = lean_array_push(v_fmts_2806_, v_fmt_2879_);
v___x_2882_ = lean_box(0);
v___x_2883_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(v_snd_2878_, v___x_2882_, v___x_2881_, v_infos_2880_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
v___y_2872_ = v___x_2883_;
goto v___jp_2871_;
}
else
{
lean_object* v_snd_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v_snd_2884_ = lean_ctor_get(v_a_2875_, 1);
lean_inc(v_snd_2884_);
lean_dec(v_a_2875_);
v___x_2885_ = lean_box(0);
v___x_2886_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(v_snd_2884_, v___x_2885_, v_fmts_2806_, v_infos_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
v___y_2872_ = v___x_2886_;
goto v___jp_2871_;
}
}
else
{
lean_object* v_a_2887_; 
v_a_2887_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2887_);
lean_dec_ref_known(v___x_2874_, 1);
v_a_2868_ = v_a_2887_;
goto v___jp_2867_;
}
v___jp_2813_:
{
lean_object* v___x_2816_; uint8_t v___x_2817_; 
v___x_2816_ = lean_array_get_size(v_fmts_2815_);
v___x_2817_ = lean_nat_dec_eq(v___x_2816_, v___x_2804_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2818_ = lean_array_to_list(v_fmts_2815_);
v___x_2819_ = ((lean_object*)(l_Lean_Elab_Info_fmtHover_x3f___lam__1___closed__1));
v___x_2820_ = l_Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0(v___x_2818_, v___x_2819_);
v___x_2821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2820_);
lean_ctor_set(v___x_2821_, 1, v___y_2814_);
v___x_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
v___x_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
return v___x_2823_;
}
else
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
lean_dec_ref(v_fmts_2815_);
lean_dec(v___y_2814_);
v___x_2824_ = lean_box(0);
v___x_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2824_);
return v___x_2825_;
}
}
v___jp_2826_:
{
if (lean_obj_tag(v___y_2827_) == 1)
{
lean_object* v_val_2830_; lean_object* v___x_2831_; 
v_val_2830_ = lean_ctor_get(v___y_2827_, 0);
lean_inc(v_val_2830_);
lean_dec_ref_known(v___y_2827_, 1);
v___x_2831_ = lean_array_push(v_fmts_2829_, v_val_2830_);
v___y_2814_ = v___y_2828_;
v_fmts_2815_ = v___x_2831_;
goto v___jp_2813_;
}
else
{
lean_dec(v___y_2827_);
v___y_2814_ = v___y_2828_;
v_fmts_2815_ = v_fmts_2829_;
goto v___jp_2813_;
}
}
v___jp_2832_:
{
lean_object* v___x_2834_; 
v___x_2834_ = l_Lean_Elab_Info_docString_x3f(v_i_2805_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_snd_2835_; lean_object* v_a_2836_; 
v_snd_2835_ = lean_ctor_get(v_a_2833_, 1);
lean_inc(v_snd_2835_);
v_a_2836_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2836_);
lean_dec_ref_known(v___x_2834_, 1);
if (lean_obj_tag(v_a_2836_) == 1)
{
lean_object* v_fst_2837_; lean_object* v_fst_2838_; lean_object* v_snd_2839_; lean_object* v_val_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2848_; 
v_fst_2837_ = lean_ctor_get(v_a_2833_, 0);
lean_inc(v_fst_2837_);
lean_dec_ref(v_a_2833_);
v_fst_2838_ = lean_ctor_get(v_snd_2835_, 0);
lean_inc(v_fst_2838_);
v_snd_2839_ = lean_ctor_get(v_snd_2835_, 1);
lean_inc(v_snd_2839_);
lean_dec(v_snd_2835_);
v_val_2840_ = lean_ctor_get(v_a_2836_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v_a_2836_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2842_ = v_a_2836_;
v_isShared_2843_ = v_isSharedCheck_2848_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_val_2840_);
lean_dec(v_a_2836_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2848_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
lean_ctor_set_tag(v___x_2842_, 3);
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_val_2840_);
v___x_2845_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
lean_object* v___x_2846_; 
v___x_2846_ = lean_array_push(v_fst_2838_, v___x_2845_);
v___y_2827_ = v_fst_2837_;
v___y_2828_ = v_snd_2839_;
v_fmts_2829_ = v___x_2846_;
goto v___jp_2826_;
}
}
}
else
{
lean_object* v_fst_2849_; lean_object* v_fst_2850_; lean_object* v_snd_2851_; 
lean_dec(v_a_2836_);
v_fst_2849_ = lean_ctor_get(v_a_2833_, 0);
lean_inc(v_fst_2849_);
lean_dec_ref(v_a_2833_);
v_fst_2850_ = lean_ctor_get(v_snd_2835_, 0);
lean_inc(v_fst_2850_);
v_snd_2851_ = lean_ctor_get(v_snd_2835_, 1);
lean_inc(v_snd_2851_);
lean_dec(v_snd_2835_);
v___y_2827_ = v_fst_2849_;
v___y_2828_ = v_snd_2851_;
v_fmts_2829_ = v_fst_2850_;
goto v___jp_2826_;
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec_ref(v_a_2833_);
v_a_2852_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2834_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2834_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
v___jp_2860_:
{
if (v___y_2862_ == 0)
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
lean_dec_ref(v___y_2861_);
v___x_2863_ = lean_box(0);
v___x_2864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2864_, 0, v_fmts_2806_);
lean_ctor_set(v___x_2864_, 1, v_infos_2807_);
v___x_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2863_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
v_a_2833_ = v___x_2865_;
goto v___jp_2832_;
}
else
{
lean_object* v___x_2866_; 
lean_dec(v_infos_2807_);
lean_dec_ref(v_fmts_2806_);
lean_dec_ref(v_i_2805_);
v___x_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2866_, 0, v___y_2861_);
return v___x_2866_;
}
}
v___jp_2867_:
{
uint8_t v___x_2869_; 
v___x_2869_ = l_Lean_Exception_isInterrupt(v_a_2868_);
if (v___x_2869_ == 0)
{
uint8_t v___x_2870_; 
lean_inc_ref(v_a_2868_);
v___x_2870_ = l_Lean_Exception_isRuntime(v_a_2868_);
v___y_2861_ = v_a_2868_;
v___y_2862_ = v___x_2870_;
goto v___jp_2860_;
}
else
{
v___y_2861_ = v_a_2868_;
v___y_2862_ = v___x_2869_;
goto v___jp_2860_;
}
}
v___jp_2871_:
{
lean_object* v_a_2873_; 
v_a_2873_ = lean_ctor_get(v___y_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref(v___y_2872_);
v_a_2833_ = v_a_2873_;
goto v___jp_2832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__1___boxed(lean_object* v___x_2888_, lean_object* v_i_2889_, lean_object* v_fmts_2890_, lean_object* v_infos_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l_Lean_Elab_Info_fmtHover_x3f___lam__1(v___x_2888_, v_i_2889_, v_fmts_2890_, v_infos_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___x_2888_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f(lean_object* v_ci_2900_, lean_object* v_i_2901_){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v_fmts_2905_; lean_object* v_infos_2906_; lean_object* v___f_2907_; lean_object* v___x_2908_; 
v___x_2903_ = l_Lean_Elab_Info_lctx(v_i_2901_);
v___x_2904_ = lean_unsigned_to_nat(0u);
v_fmts_2905_ = ((lean_object*)(l_Lean_Elab_Info_fmtHover_x3f___closed__0));
v_infos_2906_ = lean_box(1);
v___f_2907_ = lean_alloc_closure((void*)(l_Lean_Elab_Info_fmtHover_x3f___lam__1___boxed), 9, 4);
lean_closure_set(v___f_2907_, 0, v___x_2904_);
lean_closure_set(v___f_2907_, 1, v_i_2901_);
lean_closure_set(v___f_2907_, 2, v_fmts_2905_);
lean_closure_set(v___f_2907_, 3, v_infos_2906_);
v___x_2908_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ci_2900_, v___x_2903_, v___f_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___boxed(lean_object* v_ci_2909_, lean_object* v_i_2910_, lean_object* v_a_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Lean_Elab_Info_fmtHover_x3f(v_ci_2909_, v_i_2910_);
return v_res_2912_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(lean_object* v_hoverPos_2921_, lean_object* v_pos_2922_, lean_object* v_tailPos_2923_, lean_object* v_as_2924_, size_t v_i_2925_, size_t v_stop_2926_){
_start:
{
uint8_t v___x_2927_; 
v___x_2927_ = lean_usize_dec_eq(v_i_2925_, v_stop_2926_);
if (v___x_2927_ == 0)
{
lean_object* v___x_2928_; uint8_t v___x_2929_; 
v___x_2928_ = lean_array_uget_borrowed(v_as_2924_, v_i_2925_);
v___x_2929_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(v_hoverPos_2921_, v_pos_2922_, v_tailPos_2923_, v___x_2928_);
if (v___x_2929_ == 0)
{
size_t v___x_2930_; size_t v___x_2931_; 
v___x_2930_ = ((size_t)1ULL);
v___x_2931_ = lean_usize_add(v_i_2925_, v___x_2930_);
v_i_2925_ = v___x_2931_;
goto _start;
}
else
{
return v___x_2929_;
}
}
else
{
uint8_t v___x_2933_; 
v___x_2933_ = 0;
return v___x_2933_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(lean_object* v_hoverPos_2934_, lean_object* v_pos_2935_, lean_object* v_tailPos_2936_, lean_object* v_x_2937_){
_start:
{
if (lean_obj_tag(v_x_2937_) == 0)
{
lean_object* v_cs_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; 
v_cs_2938_ = lean_ctor_get(v_x_2937_, 0);
v___x_2939_ = lean_unsigned_to_nat(0u);
v___x_2940_ = lean_array_get_size(v_cs_2938_);
v___x_2941_ = lean_nat_dec_lt(v___x_2939_, v___x_2940_);
if (v___x_2941_ == 0)
{
return v___x_2941_;
}
else
{
if (v___x_2941_ == 0)
{
return v___x_2941_;
}
else
{
size_t v___x_2942_; size_t v___x_2943_; uint8_t v___x_2944_; 
v___x_2942_ = ((size_t)0ULL);
v___x_2943_ = lean_usize_of_nat(v___x_2940_);
v___x_2944_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(v_hoverPos_2934_, v_pos_2935_, v_tailPos_2936_, v_cs_2938_, v___x_2942_, v___x_2943_);
return v___x_2944_;
}
}
}
else
{
lean_object* v_vs_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; uint8_t v___x_2948_; 
v_vs_2945_ = lean_ctor_get(v_x_2937_, 0);
v___x_2946_ = lean_unsigned_to_nat(0u);
v___x_2947_ = lean_array_get_size(v_vs_2945_);
v___x_2948_ = lean_nat_dec_lt(v___x_2946_, v___x_2947_);
if (v___x_2948_ == 0)
{
return v___x_2948_;
}
else
{
if (v___x_2948_ == 0)
{
return v___x_2948_;
}
else
{
size_t v___x_2949_; size_t v___x_2950_; uint8_t v___x_2951_; 
v___x_2949_ = ((size_t)0ULL);
v___x_2950_ = lean_usize_of_nat(v___x_2947_);
v___x_2951_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_2934_, v_pos_2935_, v_tailPos_2936_, v_vs_2945_, v___x_2949_, v___x_2950_);
return v___x_2951_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(lean_object* v_hoverPos_2952_, lean_object* v_pos_2953_, lean_object* v_tailPos_2954_, lean_object* v_t_2955_){
_start:
{
lean_object* v_root_2956_; lean_object* v_tail_2957_; uint8_t v___x_2958_; 
v_root_2956_ = lean_ctor_get(v_t_2955_, 0);
v_tail_2957_ = lean_ctor_get(v_t_2955_, 1);
v___x_2958_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(v_hoverPos_2952_, v_pos_2953_, v_tailPos_2954_, v_root_2956_);
if (v___x_2958_ == 0)
{
lean_object* v___x_2959_; lean_object* v___x_2960_; uint8_t v___x_2961_; 
v___x_2959_ = lean_unsigned_to_nat(0u);
v___x_2960_ = lean_array_get_size(v_tail_2957_);
v___x_2961_ = lean_nat_dec_lt(v___x_2959_, v___x_2960_);
if (v___x_2961_ == 0)
{
return v___x_2958_;
}
else
{
if (v___x_2961_ == 0)
{
return v___x_2958_;
}
else
{
size_t v___x_2962_; size_t v___x_2963_; uint8_t v___x_2964_; 
v___x_2962_ = ((size_t)0ULL);
v___x_2963_ = lean_usize_of_nat(v___x_2960_);
v___x_2964_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_2952_, v_pos_2953_, v_tailPos_2954_, v_tail_2957_, v___x_2962_, v___x_2963_);
return v___x_2964_;
}
}
}
else
{
return v___x_2958_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(lean_object* v_hoverPos_2965_, lean_object* v_pos_2966_, lean_object* v_tailPos_2967_, lean_object* v_a_2968_){
_start:
{
if (lean_obj_tag(v_a_2968_) == 1)
{
lean_object* v_i_2969_; 
v_i_2969_ = lean_ctor_get(v_a_2968_, 0);
switch(lean_obj_tag(v_i_2969_))
{
case 0:
{
lean_object* v_children_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; uint8_t v___x_2973_; 
v_children_2970_ = lean_ctor_get(v_a_2968_, 1);
v___x_2971_ = l_Lean_Elab_Info_stx(v_i_2969_);
v___x_2972_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3));
v___x_2973_ = l_Lean_Syntax_isOfKind(v___x_2971_, v___x_2972_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; 
v___x_2974_ = l_Lean_Elab_Info_pos_x3f(v_i_2969_);
if (lean_obj_tag(v___x_2974_) == 1)
{
lean_object* v_val_2975_; lean_object* v___x_2976_; 
v_val_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_val_2975_);
lean_dec_ref_known(v___x_2974_, 1);
v___x_2976_ = l_Lean_Elab_Info_tailPos_x3f(v_i_2969_);
if (lean_obj_tag(v___x_2976_) == 1)
{
lean_object* v_val_2977_; uint8_t v___x_2978_; uint8_t v___y_2980_; uint8_t v___x_2982_; 
v_val_2977_ = lean_ctor_get(v___x_2976_, 0);
lean_inc(v_val_2977_);
lean_dec_ref_known(v___x_2976_, 1);
v___x_2978_ = 1;
v___x_2982_ = lean_nat_dec_lt(v_hoverPos_2965_, v_val_2977_);
if (v___x_2982_ == 0)
{
lean_dec(v_val_2977_);
lean_dec(v_val_2975_);
v___y_2980_ = v___x_2982_;
goto v___jp_2979_;
}
else
{
uint8_t v___x_2983_; 
v___x_2983_ = lean_nat_dec_eq(v_val_2975_, v_pos_2966_);
lean_dec(v_val_2975_);
if (v___x_2983_ == 0)
{
uint8_t v___x_2984_; 
lean_dec(v_val_2977_);
v___x_2984_ = lean_bool_not(v___x_2983_);
v___y_2980_ = v___x_2984_;
goto v___jp_2979_;
}
else
{
uint8_t v___x_2985_; uint8_t v___x_2986_; 
v___x_2985_ = lean_nat_dec_eq(v_val_2977_, v_tailPos_2967_);
lean_dec(v_val_2977_);
v___x_2986_ = lean_bool_not(v___x_2985_);
v___y_2980_ = v___x_2986_;
goto v___jp_2979_;
}
}
v___jp_2979_:
{
if (v___y_2980_ == 0)
{
uint8_t v___x_2981_; 
v___x_2981_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2965_, v_pos_2966_, v_tailPos_2967_, v_children_2970_);
return v___x_2981_;
}
else
{
return v___x_2978_;
}
}
}
else
{
uint8_t v___x_2987_; 
lean_dec(v___x_2976_);
lean_dec(v_val_2975_);
v___x_2987_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2965_, v_pos_2966_, v_tailPos_2967_, v_children_2970_);
return v___x_2987_;
}
}
else
{
uint8_t v___x_2988_; 
lean_dec(v___x_2974_);
v___x_2988_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2965_, v_pos_2966_, v_tailPos_2967_, v_children_2970_);
return v___x_2988_;
}
}
else
{
uint8_t v___x_2989_; 
v___x_2989_ = 0;
return v___x_2989_;
}
}
case 4:
{
lean_object* v_children_2990_; uint8_t v___x_2991_; 
v_children_2990_ = lean_ctor_get(v_a_2968_, 1);
v___x_2991_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2965_, v_pos_2966_, v_tailPos_2967_, v_children_2990_);
return v___x_2991_;
}
default: 
{
uint8_t v___x_2992_; 
v___x_2992_ = 0;
return v___x_2992_;
}
}
}
else
{
uint8_t v___x_2993_; 
v___x_2993_ = 0;
return v___x_2993_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(lean_object* v_hoverPos_2994_, lean_object* v_pos_2995_, lean_object* v_tailPos_2996_, lean_object* v_as_2997_, size_t v_i_2998_, size_t v_stop_2999_){
_start:
{
uint8_t v___x_3000_; 
v___x_3000_ = lean_usize_dec_eq(v_i_2998_, v_stop_2999_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; uint8_t v___x_3002_; 
v___x_3001_ = lean_array_uget_borrowed(v_as_2997_, v_i_2998_);
v___x_3002_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(v_hoverPos_2994_, v_pos_2995_, v_tailPos_2996_, v___x_3001_);
if (v___x_3002_ == 0)
{
size_t v___x_3003_; size_t v___x_3004_; 
v___x_3003_ = ((size_t)1ULL);
v___x_3004_ = lean_usize_add(v_i_2998_, v___x_3003_);
v_i_2998_ = v___x_3004_;
goto _start;
}
else
{
return v___x_3002_;
}
}
else
{
uint8_t v___x_3006_; 
v___x_3006_ = 0;
return v___x_3006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1___boxed(lean_object* v_hoverPos_3007_, lean_object* v_pos_3008_, lean_object* v_tailPos_3009_, lean_object* v_as_3010_, lean_object* v_i_3011_, lean_object* v_stop_3012_){
_start:
{
size_t v_i_boxed_3013_; size_t v_stop_boxed_3014_; uint8_t v_res_3015_; lean_object* v_r_3016_; 
v_i_boxed_3013_ = lean_unbox_usize(v_i_3011_);
lean_dec(v_i_3011_);
v_stop_boxed_3014_ = lean_unbox_usize(v_stop_3012_);
lean_dec(v_stop_3012_);
v_res_3015_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_3007_, v_pos_3008_, v_tailPos_3009_, v_as_3010_, v_i_boxed_3013_, v_stop_boxed_3014_);
lean_dec_ref(v_as_3010_);
lean_dec(v_tailPos_3009_);
lean_dec(v_pos_3008_);
lean_dec(v_hoverPos_3007_);
v_r_3016_ = lean_box(v_res_3015_);
return v_r_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1___boxed(lean_object* v_hoverPos_3017_, lean_object* v_pos_3018_, lean_object* v_tailPos_3019_, lean_object* v_as_3020_, lean_object* v_i_3021_, lean_object* v_stop_3022_){
_start:
{
size_t v_i_boxed_3023_; size_t v_stop_boxed_3024_; uint8_t v_res_3025_; lean_object* v_r_3026_; 
v_i_boxed_3023_ = lean_unbox_usize(v_i_3021_);
lean_dec(v_i_3021_);
v_stop_boxed_3024_ = lean_unbox_usize(v_stop_3022_);
lean_dec(v_stop_3022_);
v_res_3025_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(v_hoverPos_3017_, v_pos_3018_, v_tailPos_3019_, v_as_3020_, v_i_boxed_3023_, v_stop_boxed_3024_);
lean_dec_ref(v_as_3020_);
lean_dec(v_tailPos_3019_);
lean_dec(v_pos_3018_);
lean_dec(v_hoverPos_3017_);
v_r_3026_ = lean_box(v_res_3025_);
return v_r_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0___boxed(lean_object* v_hoverPos_3027_, lean_object* v_pos_3028_, lean_object* v_tailPos_3029_, lean_object* v_t_3030_){
_start:
{
uint8_t v_res_3031_; lean_object* v_r_3032_; 
v_res_3031_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_3027_, v_pos_3028_, v_tailPos_3029_, v_t_3030_);
lean_dec_ref(v_t_3030_);
lean_dec(v_tailPos_3029_);
lean_dec(v_pos_3028_);
lean_dec(v_hoverPos_3027_);
v_r_3032_ = lean_box(v_res_3031_);
return v_r_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0___boxed(lean_object* v_hoverPos_3033_, lean_object* v_pos_3034_, lean_object* v_tailPos_3035_, lean_object* v_x_3036_){
_start:
{
uint8_t v_res_3037_; lean_object* v_r_3038_; 
v_res_3037_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(v_hoverPos_3033_, v_pos_3034_, v_tailPos_3035_, v_x_3036_);
lean_dec_ref(v_x_3036_);
lean_dec(v_tailPos_3035_);
lean_dec(v_pos_3034_);
lean_dec(v_hoverPos_3033_);
v_r_3038_ = lean_box(v_res_3037_);
return v_r_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___boxed(lean_object* v_hoverPos_3039_, lean_object* v_pos_3040_, lean_object* v_tailPos_3041_, lean_object* v_a_3042_){
_start:
{
uint8_t v_res_3043_; lean_object* v_r_3044_; 
v_res_3043_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(v_hoverPos_3039_, v_pos_3040_, v_tailPos_3041_, v_a_3042_);
lean_dec_ref(v_a_3042_);
lean_dec(v_tailPos_3041_);
lean_dec(v_pos_3040_);
lean_dec(v_hoverPos_3039_);
v_r_3044_ = lean_box(v_res_3043_);
return v_r_3044_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(lean_object* v_x_3045_, lean_object* v_x_3046_){
_start:
{
if (lean_obj_tag(v_x_3045_) == 0)
{
if (lean_obj_tag(v_x_3046_) == 0)
{
uint8_t v___x_3047_; 
v___x_3047_ = 1;
return v___x_3047_;
}
else
{
uint8_t v___x_3048_; 
v___x_3048_ = 0;
return v___x_3048_;
}
}
else
{
if (lean_obj_tag(v_x_3046_) == 0)
{
uint8_t v___x_3049_; 
v___x_3049_ = 0;
return v___x_3049_;
}
else
{
lean_object* v_val_3050_; lean_object* v_val_3051_; uint8_t v___x_3052_; 
v_val_3050_ = lean_ctor_get(v_x_3045_, 0);
v_val_3051_ = lean_ctor_get(v_x_3046_, 0);
v___x_3052_ = lean_nat_dec_eq(v_val_3050_, v_val_3051_);
return v___x_3052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3___boxed(lean_object* v_x_3053_, lean_object* v_x_3054_){
_start:
{
uint8_t v_res_3055_; lean_object* v_r_3056_; 
v_res_3055_ = l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(v_x_3053_, v_x_3054_);
lean_dec(v_x_3054_);
lean_dec(v_x_3053_);
v_r_3056_ = lean_box(v_res_3055_);
return v_r_3056_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(lean_object* v_x_3057_){
_start:
{
if (lean_obj_tag(v_x_3057_) == 0)
{
uint8_t v___x_3058_; 
v___x_3058_ = 1;
return v___x_3058_;
}
else
{
lean_object* v_head_3059_; uint8_t v_indented_3060_; 
v_head_3059_ = lean_ctor_get(v_x_3057_, 0);
v_indented_3060_ = lean_ctor_get_uint8(v_head_3059_, sizeof(void*)*3 + 1);
if (v_indented_3060_ == 0)
{
return v_indented_3060_;
}
else
{
lean_object* v_tail_3061_; 
v_tail_3061_ = lean_ctor_get(v_x_3057_, 1);
v_x_3057_ = v_tail_3061_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0___boxed(lean_object* v_x_3063_){
_start:
{
uint8_t v_res_3064_; lean_object* v_r_3065_; 
v_res_3064_ = l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(v_x_3063_);
lean_dec(v_x_3063_);
v_r_3065_ = lean_box(v_res_3064_);
return v_r_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0(lean_object* v_text_3066_, lean_object* v_hoverPos_3067_, lean_object* v_ctx_3068_, lean_object* v_i_3069_, lean_object* v_cs_3070_, lean_object* v_gs_3071_){
_start:
{
if (lean_obj_tag(v_i_3069_) == 0)
{
lean_object* v_i_3072_; uint8_t v___y_3074_; uint8_t v___y_3075_; lean_object* v___y_3076_; lean_object* v___x_3080_; 
v_i_3072_ = lean_ctor_get(v_i_3069_, 0);
v___x_3080_ = l_Lean_Elab_Info_pos_x3f(v_i_3069_);
if (lean_obj_tag(v___x_3080_) == 1)
{
lean_object* v_val_3081_; lean_object* v___x_3082_; 
v_val_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_val_3081_);
lean_dec_ref_known(v___x_3080_, 1);
v___x_3082_ = l_Lean_Elab_Info_tailPos_x3f(v_i_3069_);
if (lean_obj_tag(v___x_3082_) == 1)
{
lean_object* v_val_3083_; lean_object* v_source_3084_; uint8_t v___x_3085_; 
v_val_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_val_3083_);
lean_dec_ref_known(v___x_3082_, 1);
v_source_3084_ = lean_ctor_get(v_text_3066_, 0);
v___x_3085_ = lean_nat_dec_le(v_val_3081_, v_hoverPos_3067_);
if (v___x_3085_ == 0)
{
lean_dec(v_val_3083_);
lean_dec(v_val_3081_);
lean_dec_ref(v_ctx_3068_);
lean_dec_ref(v_text_3066_);
lean_inc(v_gs_3071_);
return v_gs_3071_;
}
else
{
lean_object* v___x_3086_; lean_object* v_trailSize_3087_; lean_object* v___x_3088_; uint8_t v___y_3090_; uint8_t v___y_3100_; uint8_t v___y_3105_; lean_object* v___x_3109_; uint8_t v_atEOF_3110_; lean_object* v___y_3112_; lean_object* v___x_3115_; uint8_t v___x_3116_; 
v___x_3086_ = l_Lean_Elab_Info_stx(v_i_3069_);
v_trailSize_3087_ = l_Lean_Syntax_getTrailingSize(v___x_3086_);
lean_dec(v___x_3086_);
v___x_3088_ = lean_nat_add(v_val_3083_, v_trailSize_3087_);
v___x_3109_ = lean_string_utf8_byte_size(v_source_3084_);
v_atEOF_3110_ = lean_nat_dec_eq(v___x_3088_, v___x_3109_);
v___x_3115_ = lean_unsigned_to_nat(1u);
v___x_3116_ = lean_nat_dec_le(v___x_3115_, v_trailSize_3087_);
if (v___x_3116_ == 0)
{
lean_dec(v_trailSize_3087_);
v___y_3112_ = v___x_3115_;
goto v___jp_3111_;
}
else
{
v___y_3112_ = v_trailSize_3087_;
goto v___jp_3111_;
}
v___jp_3089_:
{
lean_object* v___x_3091_; lean_object* v_column_3092_; lean_object* v___x_3093_; lean_object* v_column_3094_; uint8_t v___x_3095_; uint8_t v___x_3096_; 
lean_inc_ref(v_text_3066_);
v___x_3091_ = l_Lean_FileMap_toPosition(v_text_3066_, v_hoverPos_3067_);
v_column_3092_ = lean_ctor_get(v___x_3091_, 1);
lean_inc(v_column_3092_);
lean_dec_ref(v___x_3091_);
v___x_3093_ = l_Lean_FileMap_toPosition(v_text_3066_, v_val_3081_);
lean_dec(v_val_3081_);
v_column_3094_ = lean_ctor_get(v___x_3093_, 1);
lean_inc(v_column_3094_);
lean_dec_ref(v___x_3093_);
v___x_3095_ = lean_nat_dec_lt(v_column_3092_, v_column_3094_);
lean_dec(v_column_3094_);
lean_dec(v_column_3092_);
v___x_3096_ = lean_nat_dec_eq(v_hoverPos_3067_, v___x_3088_);
lean_dec(v___x_3088_);
if (v___x_3096_ == 0)
{
lean_object* v___x_3097_; 
v___x_3097_ = lean_unsigned_to_nat(1u);
v___y_3074_ = v___x_3095_;
v___y_3075_ = v___y_3090_;
v___y_3076_ = v___x_3097_;
goto v___jp_3073_;
}
else
{
lean_object* v___x_3098_; 
v___x_3098_ = lean_unsigned_to_nat(0u);
v___y_3074_ = v___x_3095_;
v___y_3075_ = v___y_3090_;
v___y_3076_ = v___x_3098_;
goto v___jp_3073_;
}
}
v___jp_3099_:
{
if (v___y_3100_ == 0)
{
lean_dec(v___x_3088_);
lean_dec(v_val_3083_);
lean_dec(v_val_3081_);
lean_dec_ref(v_ctx_3068_);
lean_dec_ref(v_text_3066_);
lean_inc(v_gs_3071_);
return v_gs_3071_;
}
else
{
uint8_t v___x_3101_; 
v___x_3101_ = lean_nat_dec_lt(v_val_3081_, v_hoverPos_3067_);
if (v___x_3101_ == 0)
{
lean_dec(v_val_3083_);
v___y_3090_ = v___x_3101_;
goto v___jp_3089_;
}
else
{
uint8_t v___x_3102_; uint8_t v___x_3103_; 
v___x_3102_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_3067_, v_val_3081_, v_val_3083_, v_cs_3070_);
lean_dec(v_val_3083_);
v___x_3103_ = lean_bool_not(v___x_3102_);
v___y_3090_ = v___x_3103_;
goto v___jp_3089_;
}
}
}
v___jp_3104_:
{
if (v___y_3105_ == 0)
{
lean_dec(v___x_3088_);
lean_dec(v_val_3083_);
lean_dec(v_val_3081_);
lean_dec_ref(v_ctx_3068_);
lean_dec_ref(v_text_3066_);
lean_inc(v_gs_3071_);
return v_gs_3071_;
}
else
{
uint8_t v___x_3106_; 
v___x_3106_ = l_List_isEmpty___redArg(v_gs_3071_);
if (v___x_3106_ == 0)
{
uint8_t v___x_3107_; 
v___x_3107_ = lean_nat_dec_le(v_val_3083_, v_hoverPos_3067_);
if (v___x_3107_ == 0)
{
v___y_3100_ = v___x_3107_;
goto v___jp_3099_;
}
else
{
uint8_t v___x_3108_; 
v___x_3108_ = l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(v_gs_3071_);
v___y_3100_ = v___x_3108_;
goto v___jp_3099_;
}
}
else
{
v___y_3100_ = v___x_3106_;
goto v___jp_3099_;
}
}
}
v___jp_3111_:
{
lean_object* v___x_3113_; uint8_t v___x_3114_; 
v___x_3113_ = lean_nat_add(v_val_3083_, v___y_3112_);
lean_dec(v___y_3112_);
v___x_3114_ = lean_nat_dec_lt(v_hoverPos_3067_, v___x_3113_);
lean_dec(v___x_3113_);
if (v___x_3114_ == 0)
{
v___y_3105_ = v_atEOF_3110_;
goto v___jp_3104_;
}
else
{
v___y_3105_ = v___x_3114_;
goto v___jp_3104_;
}
}
}
}
else
{
lean_dec(v___x_3082_);
lean_dec(v_val_3081_);
lean_dec_ref(v_ctx_3068_);
lean_dec_ref(v_text_3066_);
lean_inc(v_gs_3071_);
return v_gs_3071_;
}
}
else
{
lean_dec(v___x_3080_);
lean_dec_ref(v_ctx_3068_);
lean_dec_ref(v_text_3066_);
lean_inc(v_gs_3071_);
return v_gs_3071_;
}
v___jp_3073_:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
lean_inc_ref(v_i_3072_);
v___x_3077_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3077_, 0, v_ctx_3068_);
lean_ctor_set(v___x_3077_, 1, v_i_3072_);
lean_ctor_set(v___x_3077_, 2, v___y_3076_);
lean_ctor_set_uint8(v___x_3077_, sizeof(void*)*3, v___y_3075_);
lean_ctor_set_uint8(v___x_3077_, sizeof(void*)*3 + 1, v___y_3074_);
v___x_3078_ = lean_box(0);
v___x_3079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3077_);
lean_ctor_set(v___x_3079_, 1, v___x_3078_);
return v___x_3079_;
}
}
else
{
lean_dec_ref(v_ctx_3068_);
lean_dec_ref(v_text_3066_);
lean_inc(v_gs_3071_);
return v_gs_3071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0___boxed(lean_object* v_text_3117_, lean_object* v_hoverPos_3118_, lean_object* v_ctx_3119_, lean_object* v_i_3120_, lean_object* v_cs_3121_, lean_object* v_gs_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0(v_text_3117_, v_hoverPos_3118_, v_ctx_3119_, v_i_3120_, v_cs_3121_, v_gs_3122_);
lean_dec(v_gs_3122_);
lean_dec_ref(v_cs_3121_);
lean_dec_ref(v_i_3120_);
lean_dec(v_hoverPos_3118_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(lean_object* v_a_3124_, lean_object* v_a_3125_){
_start:
{
if (lean_obj_tag(v_a_3124_) == 0)
{
lean_object* v___x_3126_; 
v___x_3126_ = l_List_reverse___redArg(v_a_3125_);
return v___x_3126_;
}
else
{
lean_object* v_head_3127_; lean_object* v_tail_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3137_; 
v_head_3127_ = lean_ctor_get(v_a_3124_, 0);
v_tail_3128_ = lean_ctor_get(v_a_3124_, 1);
v_isSharedCheck_3137_ = !lean_is_exclusive(v_a_3124_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3130_ = v_a_3124_;
v_isShared_3131_ = v_isSharedCheck_3137_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_tail_3128_);
lean_inc(v_head_3127_);
lean_dec(v_a_3124_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3137_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v_priority_3132_; lean_object* v___x_3134_; 
v_priority_3132_ = lean_ctor_get(v_head_3127_, 2);
lean_inc(v_priority_3132_);
lean_dec(v_head_3127_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 1, v_a_3125_);
lean_ctor_set(v___x_3130_, 0, v_priority_3132_);
v___x_3134_ = v___x_3130_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_priority_3132_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v_a_3125_);
v___x_3134_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
v_a_3124_ = v_tail_3128_;
v_a_3125_ = v___x_3134_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(lean_object* v_maxPrio_x3f_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_){
_start:
{
if (lean_obj_tag(v_a_3139_) == 0)
{
lean_object* v___x_3141_; 
v___x_3141_ = l_List_reverse___redArg(v_a_3140_);
return v___x_3141_;
}
else
{
lean_object* v_head_3142_; lean_object* v_tail_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3155_; 
v_head_3142_ = lean_ctor_get(v_a_3139_, 0);
v_tail_3143_ = lean_ctor_get(v_a_3139_, 1);
v_isSharedCheck_3155_ = !lean_is_exclusive(v_a_3139_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3145_ = v_a_3139_;
v_isShared_3146_ = v_isSharedCheck_3155_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_tail_3143_);
lean_inc(v_head_3142_);
lean_dec(v_a_3139_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3155_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v_priority_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; 
v_priority_3147_ = lean_ctor_get(v_head_3142_, 2);
lean_inc(v_priority_3147_);
v___x_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3148_, 0, v_priority_3147_);
v___x_3149_ = l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(v___x_3148_, v_maxPrio_x3f_3138_);
lean_dec_ref_known(v___x_3148_, 1);
if (v___x_3149_ == 0)
{
lean_del_object(v___x_3145_);
lean_dec(v_head_3142_);
v_a_3139_ = v_tail_3143_;
goto _start;
}
else
{
lean_object* v___x_3152_; 
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 1, v_a_3140_);
v___x_3152_ = v___x_3145_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_head_3142_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v_a_3140_);
v___x_3152_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
v_a_3139_ = v_tail_3143_;
v_a_3140_ = v___x_3152_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4___boxed(lean_object* v_maxPrio_x3f_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(v_maxPrio_x3f_3156_, v_a_3157_, v_a_3158_);
lean_dec(v_maxPrio_x3f_3156_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2_spec__2(lean_object* v_x_3160_, lean_object* v_x_3161_){
_start:
{
if (lean_obj_tag(v_x_3161_) == 0)
{
lean_inc(v_x_3160_);
return v_x_3160_;
}
else
{
lean_object* v_head_3162_; lean_object* v_tail_3163_; uint8_t v___x_3164_; 
v_head_3162_ = lean_ctor_get(v_x_3161_, 0);
v_tail_3163_ = lean_ctor_get(v_x_3161_, 1);
v___x_3164_ = lean_nat_dec_le(v_x_3160_, v_head_3162_);
if (v___x_3164_ == 0)
{
v_x_3161_ = v_tail_3163_;
goto _start;
}
else
{
v_x_3160_ = v_head_3162_;
v_x_3161_ = v_tail_3163_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2_spec__2___boxed(lean_object* v_x_3167_, lean_object* v_x_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2_spec__2(v_x_3167_, v_x_3168_);
lean_dec(v_x_3168_);
lean_dec(v_x_3167_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2(lean_object* v_x_3170_){
_start:
{
if (lean_obj_tag(v_x_3170_) == 0)
{
lean_object* v___x_3171_; 
v___x_3171_ = lean_box(0);
return v___x_3171_;
}
else
{
lean_object* v_head_3172_; lean_object* v_tail_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v_head_3172_ = lean_ctor_get(v_x_3170_, 0);
v_tail_3173_ = lean_ctor_get(v_x_3170_, 1);
v___x_3174_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2_spec__2(v_head_3172_, v_tail_3173_);
v___x_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3174_);
return v___x_3175_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2___boxed(lean_object* v_x_3176_){
_start:
{
lean_object* v_res_3177_; 
v_res_3177_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2(v_x_3176_);
lean_dec(v_x_3176_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f(lean_object* v_text_3178_, lean_object* v_t_3179_, lean_object* v_hoverPos_3180_){
_start:
{
lean_object* v___f_3181_; lean_object* v_gs_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v_maxPrio_x3f_3185_; lean_object* v___x_3186_; 
v___f_3181_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0___boxed), 6, 2);
lean_closure_set(v___f_3181_, 0, v_text_3178_);
lean_closure_set(v___f_3181_, 1, v_hoverPos_3180_);
v_gs_3182_ = l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg(v___f_3181_, v_t_3179_);
v___x_3183_ = lean_box(0);
lean_inc(v_gs_3182_);
v___x_3184_ = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(v_gs_3182_, v___x_3183_);
v_maxPrio_x3f_3185_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2(v___x_3184_);
lean_dec(v___x_3184_);
v___x_3186_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(v_maxPrio_x3f_3185_, v_gs_3182_, v___x_3183_);
lean_dec(v_maxPrio_x3f_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(lean_object* v___x_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_){
_start:
{
if (lean_obj_tag(v_a_3188_) == 0)
{
lean_object* v___x_3190_; 
v___x_3190_ = l_List_reverse___redArg(v_a_3189_);
return v___x_3190_;
}
else
{
lean_object* v_head_3191_; lean_object* v_snd_3192_; lean_object* v_tail_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3208_; 
v_head_3191_ = lean_ctor_get(v_a_3188_, 0);
lean_inc(v_head_3191_);
v_snd_3192_ = lean_ctor_get(v_head_3191_, 1);
v_tail_3193_ = lean_ctor_get(v_a_3188_, 1);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_a_3188_);
if (v_isSharedCheck_3208_ == 0)
{
lean_object* v_unused_3209_; 
v_unused_3209_ = lean_ctor_get(v_a_3188_, 0);
lean_dec(v_unused_3209_);
v___x_3195_ = v_a_3188_;
v_isShared_3196_ = v_isSharedCheck_3208_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_tail_3193_);
lean_dec(v_a_3188_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3208_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v_info_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; uint8_t v___x_3201_; uint8_t v___x_3202_; 
v_info_3197_ = lean_ctor_get(v_snd_3192_, 1);
v___x_3198_ = l_Lean_Elab_Info_stx(v_info_3197_);
v___x_3199_ = lean_unsigned_to_nat(0u);
v___x_3200_ = l_Lean_Syntax_getArg(v___x_3187_, v___x_3199_);
v___x_3201_ = l_Lean_Syntax_structEq(v___x_3198_, v___x_3200_);
v___x_3202_ = lean_bool_not(v___x_3201_);
if (v___x_3202_ == 0)
{
lean_del_object(v___x_3195_);
lean_dec(v_head_3191_);
v_a_3188_ = v_tail_3193_;
goto _start;
}
else
{
lean_object* v___x_3205_; 
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 1, v_a_3189_);
v___x_3205_ = v___x_3195_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_head_3191_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v_a_3189_);
v___x_3205_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
v_a_3188_ = v_tail_3193_;
v_a_3189_ = v___x_3205_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0___boxed(lean_object* v___x_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(v___x_3210_, v_a_3211_, v_a_3212_);
lean_dec(v___x_3210_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0(lean_object* v_ctx_3220_, lean_object* v_info_3221_, lean_object* v_children_3222_, lean_object* v_results_3223_){
_start:
{
lean_object* v___x_3224_; uint8_t v___y_3226_; lean_object* v___x_3229_; uint8_t v___x_3230_; 
v___x_3224_ = l_Lean_Elab_Info_stx(v_info_3221_);
v___x_3229_ = ((lean_object*)(l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1));
lean_inc(v___x_3224_);
v___x_3230_ = l_Lean_Syntax_isOfKind(v___x_3224_, v___x_3229_);
if (v___x_3230_ == 0)
{
v___y_3226_ = v___x_3230_;
goto v___jp_3225_;
}
else
{
lean_object* v___x_3231_; lean_object* v___x_3232_; uint8_t v___x_3233_; 
v___x_3231_ = lean_unsigned_to_nat(0u);
v___x_3232_ = l_Lean_Syntax_getArg(v___x_3224_, v___x_3231_);
v___x_3233_ = l_Lean_Syntax_isIdent(v___x_3232_);
lean_dec(v___x_3232_);
v___y_3226_ = v___x_3233_;
goto v___jp_3225_;
}
v___jp_3225_:
{
if (v___y_3226_ == 0)
{
lean_dec(v___x_3224_);
return v_results_3223_;
}
else
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = lean_box(0);
v___x_3228_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(v___x_3224_, v_results_3223_, v___x_3227_);
lean_dec(v___x_3224_);
return v___x_3228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___boxed(lean_object* v_ctx_3234_, lean_object* v_info_3235_, lean_object* v_children_3236_, lean_object* v_results_3237_){
_start:
{
lean_object* v_res_3238_; 
v_res_3238_ = l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0(v_ctx_3234_, v_info_3235_, v_children_3236_, v_results_3237_);
lean_dec_ref(v_children_3236_);
lean_dec_ref(v_info_3235_);
lean_dec_ref(v_ctx_3234_);
return v_res_3238_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(lean_object* v_x_3239_, lean_object* v_x_3240_){
_start:
{
if (lean_obj_tag(v_x_3239_) == 0)
{
if (lean_obj_tag(v_x_3240_) == 0)
{
uint8_t v___x_3241_; 
v___x_3241_ = 1;
return v___x_3241_;
}
else
{
uint8_t v___x_3242_; 
v___x_3242_ = 0;
return v___x_3242_;
}
}
else
{
if (lean_obj_tag(v_x_3240_) == 0)
{
uint8_t v___x_3243_; 
v___x_3243_ = 0;
return v___x_3243_;
}
else
{
lean_object* v_val_3244_; lean_object* v_val_3245_; uint8_t v___x_3246_; 
v_val_3244_ = lean_ctor_get(v_x_3239_, 0);
v_val_3245_ = lean_ctor_get(v_x_3240_, 0);
v___x_3246_ = l_Lean_Elab_instBEqHoverableInfoPrio_beq(v_val_3244_, v_val_3245_);
return v___x_3246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4___boxed(lean_object* v_x_3247_, lean_object* v_x_3248_){
_start:
{
uint8_t v_res_3249_; lean_object* v_r_3250_; 
v_res_3249_ = l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(v_x_3247_, v_x_3248_);
lean_dec(v_x_3248_);
lean_dec(v_x_3247_);
v_r_3250_ = lean_box(v_res_3249_);
return v_r_3250_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5(lean_object* v_maxPrio_x3f_3251_, lean_object* v_x_3252_){
_start:
{
if (lean_obj_tag(v_x_3252_) == 0)
{
lean_object* v___x_3253_; 
v___x_3253_ = lean_box(0);
return v___x_3253_;
}
else
{
lean_object* v_head_3254_; lean_object* v_tail_3255_; lean_object* v_fst_3256_; lean_object* v___x_3257_; uint8_t v___x_3258_; 
v_head_3254_ = lean_ctor_get(v_x_3252_, 0);
v_tail_3255_ = lean_ctor_get(v_x_3252_, 1);
v_fst_3256_ = lean_ctor_get(v_head_3254_, 0);
lean_inc(v_fst_3256_);
v___x_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3257_, 0, v_fst_3256_);
v___x_3258_ = l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(v___x_3257_, v_maxPrio_x3f_3251_);
lean_dec_ref_known(v___x_3257_, 1);
if (v___x_3258_ == 0)
{
v_x_3252_ = v_tail_3255_;
goto _start;
}
else
{
lean_object* v___x_3260_; 
lean_inc(v_head_3254_);
v___x_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3260_, 0, v_head_3254_);
return v___x_3260_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5___boxed(lean_object* v_maxPrio_x3f_3261_, lean_object* v_x_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5(v_maxPrio_x3f_3261_, v_x_3262_);
lean_dec(v_x_3262_);
lean_dec(v_maxPrio_x3f_3261_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(lean_object* v_x_3264_, lean_object* v_x_3265_){
_start:
{
if (lean_obj_tag(v_x_3265_) == 0)
{
lean_inc_ref(v_x_3264_);
return v_x_3264_;
}
else
{
lean_object* v_head_3266_; lean_object* v_tail_3267_; uint8_t v___x_3268_; 
v_head_3266_ = lean_ctor_get(v_x_3265_, 0);
v_tail_3267_ = lean_ctor_get(v_x_3265_, 1);
v___x_3268_ = l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(v_x_3264_, v_head_3266_);
if (v___x_3268_ == 2)
{
v_x_3265_ = v_tail_3267_;
goto _start;
}
else
{
v_x_3264_ = v_head_3266_;
v_x_3265_ = v_tail_3267_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4___boxed(lean_object* v_x_3271_, lean_object* v_x_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(v_x_3271_, v_x_3272_);
lean_dec(v_x_3272_);
lean_dec_ref(v_x_3271_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(lean_object* v_x_3274_){
_start:
{
if (lean_obj_tag(v_x_3274_) == 0)
{
lean_object* v___x_3275_; 
v___x_3275_ = lean_box(0);
return v___x_3275_;
}
else
{
lean_object* v_head_3276_; lean_object* v_tail_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
v_head_3276_ = lean_ctor_get(v_x_3274_, 0);
v_tail_3277_ = lean_ctor_get(v_x_3274_, 1);
v___x_3278_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(v_head_3276_, v_tail_3277_);
v___x_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
return v___x_3279_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3___boxed(lean_object* v_x_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(v_x_3280_);
lean_dec(v_x_3280_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__1(lean_object* v_a_3282_, lean_object* v_a_3283_){
_start:
{
if (lean_obj_tag(v_a_3282_) == 0)
{
lean_object* v___x_3284_; 
v___x_3284_ = lean_array_to_list(v_a_3283_);
return v___x_3284_;
}
else
{
lean_object* v_head_3285_; 
v_head_3285_ = lean_ctor_get(v_a_3282_, 0);
if (lean_obj_tag(v_head_3285_) == 0)
{
lean_object* v_tail_3286_; 
v_tail_3286_ = lean_ctor_get(v_a_3282_, 1);
lean_inc(v_tail_3286_);
lean_dec_ref_known(v_a_3282_, 2);
v_a_3282_ = v_tail_3286_;
goto _start;
}
else
{
lean_object* v_val_3288_; 
v_val_3288_ = lean_ctor_get(v_head_3285_, 0);
if (lean_obj_tag(v_val_3288_) == 0)
{
lean_object* v_tail_3289_; 
v_tail_3289_ = lean_ctor_get(v_a_3282_, 1);
lean_inc(v_tail_3289_);
lean_dec_ref_known(v_a_3282_, 2);
v_a_3282_ = v_tail_3289_;
goto _start;
}
else
{
lean_object* v_tail_3291_; lean_object* v_val_3292_; lean_object* v___x_3293_; 
lean_inc_ref(v_val_3288_);
v_tail_3291_ = lean_ctor_get(v_a_3282_, 1);
lean_inc(v_tail_3291_);
lean_dec_ref_known(v_a_3282_, 2);
v_val_3292_ = lean_ctor_get(v_val_3288_, 0);
lean_inc(v_val_3292_);
lean_dec_ref_known(v_val_3288_, 1);
v___x_3293_ = lean_array_push(v_a_3283_, v_val_3292_);
v_a_3282_ = v_tail_3291_;
v_a_3283_ = v___x_3293_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__2(lean_object* v_a_3295_, lean_object* v_a_3296_){
_start:
{
if (lean_obj_tag(v_a_3295_) == 0)
{
lean_object* v___x_3297_; 
v___x_3297_ = l_List_reverse___redArg(v_a_3296_);
return v___x_3297_;
}
else
{
lean_object* v_head_3298_; lean_object* v_tail_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3308_; 
v_head_3298_ = lean_ctor_get(v_a_3295_, 0);
v_tail_3299_ = lean_ctor_get(v_a_3295_, 1);
v_isSharedCheck_3308_ = !lean_is_exclusive(v_a_3295_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3301_ = v_a_3295_;
v_isShared_3302_ = v_isSharedCheck_3308_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_tail_3299_);
lean_inc(v_head_3298_);
lean_dec(v_a_3295_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3308_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v_fst_3303_; lean_object* v___x_3305_; 
v_fst_3303_ = lean_ctor_get(v_head_3298_, 0);
lean_inc(v_fst_3303_);
lean_dec(v_head_3298_);
if (v_isShared_3302_ == 0)
{
lean_ctor_set(v___x_3301_, 1, v_a_3296_);
lean_ctor_set(v___x_3301_, 0, v_fst_3303_);
v___x_3305_ = v___x_3301_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_fst_3303_);
lean_ctor_set(v_reuseFailAlloc_3307_, 1, v_a_3296_);
v___x_3305_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
v_a_3295_ = v_tail_3299_;
v_a_3296_ = v___x_3305_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1(lean_object* v_filter_3309_, lean_object* v_hoverPos_3310_, uint8_t v_includeStop_3311_, lean_object* v_ctx_3312_, lean_object* v_info_3313_, lean_object* v_children_3314_, lean_object* v_results_3315_){
_start:
{
uint8_t v___y_3317_; lean_object* v___y_3318_; uint8_t v___y_3319_; uint8_t v___y_3320_; uint8_t v___y_3326_; uint8_t v___y_3327_; uint8_t v___y_3328_; lean_object* v___y_3329_; uint8_t v___y_3330_; uint8_t v___y_3332_; lean_object* v___y_3333_; uint8_t v___y_3334_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v_maxPrio_x3f_3347_; lean_object* v_bestResult_x3f_3348_; 
v___x_3342_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___closed__0));
v___x_3343_ = l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__1(v_results_3315_, v___x_3342_);
lean_inc_ref(v_children_3314_);
lean_inc_ref(v_info_3313_);
lean_inc_ref(v_ctx_3312_);
v___x_3344_ = lean_apply_4(v_filter_3309_, v_ctx_3312_, v_info_3313_, v_children_3314_, v___x_3343_);
v___x_3345_ = lean_box(0);
lean_inc(v___x_3344_);
v___x_3346_ = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__2(v___x_3344_, v___x_3345_);
v_maxPrio_x3f_3347_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(v___x_3346_);
lean_dec(v___x_3346_);
v_bestResult_x3f_3348_ = l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5(v_maxPrio_x3f_3347_, v___x_3344_);
lean_dec(v___x_3344_);
lean_dec(v_maxPrio_x3f_3347_);
if (lean_obj_tag(v_bestResult_x3f_3348_) == 1)
{
lean_dec_ref(v_children_3314_);
lean_dec_ref(v_info_3313_);
lean_dec_ref(v_ctx_3312_);
return v_bestResult_x3f_3348_;
}
else
{
lean_object* v___x_3349_; uint8_t v___y_3351_; uint8_t v___y_3352_; uint8_t v___y_3360_; lean_object* v___x_3364_; uint8_t v___x_3365_; 
lean_dec(v_bestResult_x3f_3348_);
v___x_3349_ = l_Lean_Elab_Info_stx(v_info_3313_);
v___x_3364_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__1));
lean_inc(v___x_3349_);
v___x_3365_ = l_Lean_Syntax_isOfKind(v___x_3349_, v___x_3364_);
if (v___x_3365_ == 0)
{
lean_object* v___x_3366_; 
lean_inc_ref(v_info_3313_);
v___x_3366_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_3313_);
if (lean_obj_tag(v___x_3366_) == 0)
{
v___y_3360_ = v___x_3365_;
goto v___jp_3359_;
}
else
{
lean_object* v_val_3367_; lean_object* v_elaborator_3368_; lean_object* v___x_3369_; uint8_t v___x_3370_; 
v_val_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_val_3367_);
lean_dec_ref_known(v___x_3366_, 1);
v_elaborator_3368_ = lean_ctor_get(v_val_3367_, 0);
lean_inc(v_elaborator_3368_);
lean_dec(v_val_3367_);
v___x_3369_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6));
v___x_3370_ = lean_name_eq(v_elaborator_3368_, v___x_3369_);
lean_dec(v_elaborator_3368_);
v___y_3360_ = v___x_3370_;
goto v___jp_3359_;
}
}
else
{
v___y_3360_ = v___x_3365_;
goto v___jp_3359_;
}
v___jp_3350_:
{
lean_object* v___x_3353_; 
v___x_3353_ = l_Lean_Syntax_getRange_x3f(v___x_3349_, v___y_3351_);
lean_dec(v___x_3349_);
if (lean_obj_tag(v___x_3353_) == 1)
{
lean_object* v_val_3354_; uint8_t v___x_3355_; uint8_t v___x_3356_; 
v_val_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc(v_val_3354_);
lean_dec_ref_known(v___x_3353_, 1);
v___x_3355_ = l_Lean_Syntax_Range_contains(v_val_3354_, v_hoverPos_3310_, v_includeStop_3311_);
v___x_3356_ = lean_bool_not(v___x_3355_);
if (v___x_3356_ == 0)
{
uint8_t v___x_3357_; 
v___x_3357_ = lean_bool_not(v___y_3352_);
v___y_3332_ = v___y_3351_;
v___y_3333_ = v_val_3354_;
v___y_3334_ = v___x_3357_;
goto v___jp_3331_;
}
else
{
v___y_3332_ = v___y_3351_;
v___y_3333_ = v_val_3354_;
v___y_3334_ = v___x_3356_;
goto v___jp_3331_;
}
}
else
{
lean_object* v___x_3358_; 
lean_dec(v___x_3353_);
lean_dec_ref(v_children_3314_);
lean_dec_ref(v_info_3313_);
lean_dec_ref(v_ctx_3312_);
v___x_3358_ = lean_box(0);
return v___x_3358_;
}
}
v___jp_3359_:
{
if (v___y_3360_ == 0)
{
uint8_t v___x_3361_; 
v___x_3361_ = 1;
switch(lean_obj_tag(v_info_3313_))
{
case 7:
{
v___y_3351_ = v___x_3361_;
v___y_3352_ = v___x_3361_;
goto v___jp_3350_;
}
case 5:
{
v___y_3351_ = v___x_3361_;
v___y_3352_ = v___x_3361_;
goto v___jp_3350_;
}
case 6:
{
v___y_3351_ = v___x_3361_;
v___y_3352_ = v___x_3361_;
goto v___jp_3350_;
}
default: 
{
lean_object* v___x_3362_; 
lean_inc_ref(v_info_3313_);
v___x_3362_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_3313_);
if (lean_obj_tag(v___x_3362_) == 0)
{
v___y_3351_ = v___x_3361_;
v___y_3352_ = v___y_3360_;
goto v___jp_3350_;
}
else
{
lean_dec_ref_known(v___x_3362_, 1);
v___y_3351_ = v___x_3361_;
v___y_3352_ = v___x_3361_;
goto v___jp_3350_;
}
}
}
}
else
{
lean_object* v___x_3363_; 
lean_dec(v___x_3349_);
lean_dec_ref(v_children_3314_);
lean_dec_ref(v_info_3313_);
lean_dec_ref(v_ctx_3312_);
v___x_3363_ = lean_box(0);
return v___x_3363_;
}
}
}
v___jp_3316_:
{
lean_object* v_priority_3321_; lean_object* v_result_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v_priority_3321_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_priority_3321_, 0, v___y_3318_);
lean_ctor_set_uint8(v_priority_3321_, sizeof(void*)*1, v___y_3319_);
lean_ctor_set_uint8(v_priority_3321_, sizeof(void*)*1 + 1, v___y_3317_);
lean_ctor_set_uint8(v_priority_3321_, sizeof(void*)*1 + 2, v___y_3320_);
v_result_3322_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_result_3322_, 0, v_ctx_3312_);
lean_ctor_set(v_result_3322_, 1, v_info_3313_);
lean_ctor_set(v_result_3322_, 2, v_children_3314_);
v___x_3323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3323_, 0, v_priority_3321_);
lean_ctor_set(v___x_3323_, 1, v_result_3322_);
v___x_3324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
return v___x_3324_;
}
v___jp_3325_:
{
if (lean_obj_tag(v_info_3313_) == 2)
{
v___y_3317_ = v___y_3330_;
v___y_3318_ = v___y_3329_;
v___y_3319_ = v___y_3328_;
v___y_3320_ = v___y_3326_;
goto v___jp_3316_;
}
else
{
v___y_3317_ = v___y_3330_;
v___y_3318_ = v___y_3329_;
v___y_3319_ = v___y_3328_;
v___y_3320_ = v___y_3327_;
goto v___jp_3316_;
}
}
v___jp_3331_:
{
if (v___y_3334_ == 0)
{
lean_object* v_start_3335_; lean_object* v_stop_3336_; uint8_t v___x_3337_; lean_object* v___x_3338_; 
v_start_3335_ = lean_ctor_get(v___y_3333_, 0);
lean_inc(v_start_3335_);
v_stop_3336_ = lean_ctor_get(v___y_3333_, 1);
lean_inc(v_stop_3336_);
lean_dec_ref(v___y_3333_);
v___x_3337_ = lean_nat_dec_eq(v_stop_3336_, v_hoverPos_3310_);
v___x_3338_ = lean_nat_sub(v_stop_3336_, v_start_3335_);
lean_dec(v_start_3335_);
lean_dec(v_stop_3336_);
if (lean_obj_tag(v_info_3313_) == 1)
{
lean_object* v_i_3339_; lean_object* v_expr_3340_; 
v_i_3339_ = lean_ctor_get(v_info_3313_, 0);
v_expr_3340_ = lean_ctor_get(v_i_3339_, 3);
if (lean_obj_tag(v_expr_3340_) == 1)
{
v___y_3326_ = v___y_3332_;
v___y_3327_ = v___y_3334_;
v___y_3328_ = v___x_3337_;
v___y_3329_ = v___x_3338_;
v___y_3330_ = v___y_3332_;
goto v___jp_3325_;
}
else
{
v___y_3326_ = v___y_3332_;
v___y_3327_ = v___y_3334_;
v___y_3328_ = v___x_3337_;
v___y_3329_ = v___x_3338_;
v___y_3330_ = v___y_3334_;
goto v___jp_3325_;
}
}
else
{
v___y_3326_ = v___y_3332_;
v___y_3327_ = v___y_3334_;
v___y_3328_ = v___x_3337_;
v___y_3329_ = v___x_3338_;
v___y_3330_ = v___y_3334_;
goto v___jp_3325_;
}
}
else
{
lean_object* v___x_3341_; 
lean_dec_ref(v___y_3333_);
lean_dec_ref(v_children_3314_);
lean_dec_ref(v_info_3313_);
lean_dec_ref(v_ctx_3312_);
v___x_3341_ = lean_box(0);
return v___x_3341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1___boxed(lean_object* v_filter_3371_, lean_object* v_hoverPos_3372_, lean_object* v_includeStop_3373_, lean_object* v_ctx_3374_, lean_object* v_info_3375_, lean_object* v_children_3376_, lean_object* v_results_3377_){
_start:
{
uint8_t v_includeStop_boxed_3378_; lean_object* v_res_3379_; 
v_includeStop_boxed_3378_ = lean_unbox(v_includeStop_3373_);
v_res_3379_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1(v_filter_3371_, v_hoverPos_3372_, v_includeStop_boxed_3378_, v_ctx_3374_, v_info_3375_, v_children_3376_, v_results_3377_);
lean_dec(v_hoverPos_3372_);
return v_res_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(lean_object* v_t_3380_, lean_object* v_hoverPos_3381_, uint8_t v_includeStop_3382_, lean_object* v_filter_3383_){
_start:
{
lean_object* v___f_3384_; lean_object* v___x_3385_; lean_object* v_postNode_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___f_3384_ = ((lean_object*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___closed__0));
v___x_3385_ = lean_box(v_includeStop_3382_);
v_postNode_3386_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1___boxed), 7, 3);
lean_closure_set(v_postNode_3386_, 0, v_filter_3383_);
lean_closure_set(v_postNode_3386_, 1, v_hoverPos_3381_);
lean_closure_set(v_postNode_3386_, 2, v___x_3385_);
v___x_3387_ = lean_box(0);
v___x_3388_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v___f_3384_, v_postNode_3386_, v___x_3387_, v_t_3380_);
if (lean_obj_tag(v___x_3388_) == 0)
{
return v___x_3387_;
}
else
{
lean_object* v_val_3389_; 
v_val_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_val_3389_);
lean_dec_ref_known(v___x_3388_, 1);
if (lean_obj_tag(v_val_3389_) == 0)
{
return v___x_3387_;
}
else
{
lean_object* v_val_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3402_; 
v_val_3390_ = lean_ctor_get(v_val_3389_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v_val_3389_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3392_ = v_val_3389_;
v_isShared_3393_ = v_isSharedCheck_3402_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_val_3390_);
lean_dec(v_val_3389_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3402_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v_snd_3394_; lean_object* v_info_3395_; lean_object* v___x_3397_; 
v_snd_3394_ = lean_ctor_get(v_val_3390_, 1);
lean_inc(v_snd_3394_);
lean_dec(v_val_3390_);
v_info_3395_ = lean_ctor_get(v_snd_3394_, 1);
lean_inc_ref(v_info_3395_);
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 0, v_snd_3394_);
v___x_3397_ = v___x_3392_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_snd_3394_);
v___x_3397_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
if (lean_obj_tag(v_info_3395_) == 1)
{
lean_object* v_i_3398_; lean_object* v_expr_3399_; uint8_t v___x_3400_; 
v_i_3398_ = lean_ctor_get(v_info_3395_, 0);
lean_inc_ref(v_i_3398_);
lean_dec_ref_known(v_info_3395_, 1);
v_expr_3399_ = lean_ctor_get(v_i_3398_, 3);
lean_inc_ref(v_expr_3399_);
lean_dec_ref(v_i_3398_);
v___x_3400_ = l_Lean_Expr_isSyntheticSorry(v_expr_3399_);
lean_dec_ref(v_expr_3399_);
if (v___x_3400_ == 0)
{
return v___x_3397_;
}
else
{
lean_dec_ref(v___x_3397_);
return v___x_3387_;
}
}
else
{
lean_dec_ref(v_info_3395_);
return v___x_3397_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___boxed(lean_object* v_t_3403_, lean_object* v_hoverPos_3404_, lean_object* v_includeStop_3405_, lean_object* v_filter_3406_){
_start:
{
uint8_t v_includeStop_boxed_3407_; lean_object* v_res_3408_; 
v_includeStop_boxed_3407_ = lean_unbox(v_includeStop_3405_);
v_res_3408_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(v_t_3403_, v_hoverPos_3404_, v_includeStop_boxed_3407_, v_filter_3406_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f(lean_object* v_t_3410_, lean_object* v_hoverPos_3411_){
_start:
{
lean_object* v_filter_3412_; uint8_t v___x_3413_; lean_object* v___x_3414_; 
v_filter_3412_ = ((lean_object*)(l_Lean_Elab_InfoTree_termGoalAt_x3f___closed__0));
v___x_3413_ = 1;
v___x_3414_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(v_t_3410_, v_hoverPos_3411_, v___x_3413_, v_filter_3412_);
return v___x_3414_;
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
