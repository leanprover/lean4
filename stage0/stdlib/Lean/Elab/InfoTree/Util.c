// Lean compiler output
// Module: Lean.Elab.InfoTree.Util
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
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Elab_Info_stx(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentArray_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_isSyntheticSorry(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTrailingSize(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t l_Lean_Syntax_isToken(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "_private.Lean.Elab.InfoTree.Util.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.InfoTree.Util"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodes___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodes___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodes(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfo___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "*import "};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__2_value)}};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "```lean\n"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\n```"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__2_value)}};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__4 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__4_value)}};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__2 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__2_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__1 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__1_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__0 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock___closed__0 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__0(lean_object* v_toPure_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3_, 0, v_a_2_);
v___x_4_ = lean_apply_2(v_toPure_1_, lean_box(0), v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__2(lean_object* v_postNode_5_, lean_object* v_val_6_, lean_object* v_i_7_, lean_object* v_children_8_, lean_object* v_toBind_9_, lean_object* v___f_10_, lean_object* v_as_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_apply_4(v_postNode_5_, v_val_6_, v_i_7_, v_children_8_, v_as_11_);
v___x_13_ = lean_apply_4(v_toBind_9_, lean_box(0), lean_box(0), v___x_12_, v___f_10_);
return v___x_13_;
}
}
static lean_object* _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_17_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__2));
v___x_18_ = lean_unsigned_to_nat(21u);
v___x_19_ = lean_unsigned_to_nat(65u);
v___x_20_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__1));
v___x_21_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__0));
v___x_22_ = l_mkPanicMessageWithDecl(v___x_21_, v___x_20_, v___x_19_, v___x_18_, v___x_17_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1___boxed(lean_object* v_postNode_23_, lean_object* v_val_24_, lean_object* v_i_25_, lean_object* v_children_26_, lean_object* v_toBind_27_, lean_object* v___f_28_, lean_object* v_x_29_, lean_object* v_inst_30_, lean_object* v_preNode_31_, lean_object* v___f_32_, lean_object* v_visitChildren_33_){
_start:
{
uint8_t v_visitChildren_boxed_34_; lean_object* v_res_35_; 
v_visitChildren_boxed_34_ = lean_unbox(v_visitChildren_33_);
v_res_35_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1(v_postNode_23_, v_val_24_, v_i_25_, v_children_26_, v_toBind_27_, v___f_28_, v_x_29_, v_inst_30_, v_preNode_31_, v___f_32_, v_visitChildren_boxed_34_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg(lean_object* v_inst_36_, lean_object* v_preNode_37_, lean_object* v_postNode_38_, lean_object* v_x_39_, lean_object* v_x_40_){
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
v___x_47_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3);
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
v___f_55_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__0), 2, 1);
lean_closure_set(v___f_55_, 0, v_toPure_51_);
lean_inc_ref(v___f_55_);
lean_inc(v_postNode_38_);
v___f_56_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__2), 7, 6);
lean_closure_set(v___f_56_, 0, v_postNode_38_);
lean_closure_set(v___f_56_, 1, v_val_54_);
lean_closure_set(v___f_56_, 2, v_i_52_);
lean_closure_set(v___f_56_, 3, v_children_53_);
lean_closure_set(v___f_56_, 4, v_toBind_50_);
lean_closure_set(v___f_56_, 5, v___f_55_);
lean_inc(v_preNode_37_);
v___f_57_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1___boxed), 11, 10);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1(lean_object* v_postNode_64_, lean_object* v_val_65_, lean_object* v_i_66_, lean_object* v_children_67_, lean_object* v_toBind_68_, lean_object* v___f_69_, lean_object* v_x_70_, lean_object* v_inst_71_, lean_object* v_preNode_72_, lean_object* v___f_73_, uint8_t v_visitChildren_74_){
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
v___x_79_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg), 5, 4);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go(lean_object* v_m_84_, lean_object* v_00_u03b1_85_, lean_object* v_inst_86_, lean_object* v_preNode_87_, lean_object* v_postNode_88_, lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_86_, v_preNode_87_, v_postNode_88_, v_x_89_, v_x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM___redArg(lean_object* v_inst_92_, lean_object* v_preNode_93_, lean_object* v_postNode_94_, lean_object* v_ctx_x3f_95_, lean_object* v_x_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_92_, v_preNode_93_, v_postNode_94_, v_ctx_x3f_95_, v_x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM(lean_object* v_m_98_, lean_object* v_00_u03b1_99_, lean_object* v_inst_100_, lean_object* v_preNode_101_, lean_object* v_postNode_102_, lean_object* v_ctx_x3f_103_, lean_object* v_x_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_100_, v_preNode_101_, v_postNode_102_, v_ctx_x3f_103_, v_x_104_);
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
v___x_127_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_118_, v_preNode_119_, v___f_126_, v_ctx_x3f_121_, v_t_122_);
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
v___x_179_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_168_, v___f_177_, v___f_176_, v___x_178_, v_i_170_);
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
lean_dec_ref_known(v_a_193_, 2);
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
lean_dec_ref_known(v_a_200_, 2);
v_a_200_ = v_tail_204_;
goto _start;
}
else
{
lean_object* v_tail_206_; lean_object* v_val_207_; lean_object* v___x_208_; 
lean_inc_ref(v_head_203_);
v_tail_206_ = lean_ctor_get(v_a_200_, 1);
lean_inc(v_tail_206_);
lean_dec_ref_known(v_a_200_, 2);
v_val_207_ = lean_ctor_get(v_head_203_, 0);
lean_inc(v_val_207_);
lean_dec_ref_known(v_head_203_, 1);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg(lean_object* v_msg_226_){
_start:
{
lean_object* v___f_227_; lean_object* v___f_228_; lean_object* v___f_229_; lean_object* v___f_230_; lean_object* v___f_231_; lean_object* v___f_232_; lean_object* v___f_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___f_227_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__0));
v___f_228_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__1));
v___f_229_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__2));
v___f_230_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__3));
v___f_231_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__4));
v___f_232_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__5));
v___f_233_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__6));
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(lean_object* v_preNode_240_, lean_object* v_postNode_241_, lean_object* v_x_242_, lean_object* v_x_243_){
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
lean_dec_ref_known(v_x_243_, 2);
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
lean_dec_ref_known(v_x_243_, 2);
lean_dec(v_postNode_241_);
lean_dec_ref(v_preNode_240_);
v___x_248_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3);
v___x_249_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg(v___x_248_);
return v___x_249_;
}
else
{
lean_object* v_i_250_; lean_object* v_children_251_; lean_object* v_val_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v_i_250_ = lean_ctor_get(v_x_243_, 0);
lean_inc_ref_n(v_i_250_, 2);
v_children_251_ = lean_ctor_get(v_x_243_, 1);
lean_inc_ref_n(v_children_251_, 2);
lean_dec_ref_known(v_x_243_, 2);
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
v___x_268_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4___redArg(v_preNode_240_, v_postNode_241_, v___x_265_, v___x_266_, v___x_267_);
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
lean_dec_ref_known(v_x_243_, 1);
lean_dec(v_x_242_);
lean_dec(v_postNode_241_);
lean_dec_ref(v_preNode_240_);
v___x_271_ = lean_box(0);
return v___x_271_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4___redArg(lean_object* v_preNode_272_, lean_object* v_postNode_273_, lean_object* v___x_274_, lean_object* v_x_275_, lean_object* v_x_276_){
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
v___x_283_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v_preNode_272_, v_postNode_273_, v___x_274_, v_head_278_);
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
v___x_304_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v___f_302_, v___f_301_, v___x_303_, v_i_300_);
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
lean_dec_ref_known(v___x_304_, 1);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_327_, lean_object* v_msg_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg(v_msg_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2(lean_object* v_00_u03b1_330_, lean_object* v_preNode_331_, lean_object* v_postNode_332_, lean_object* v_x_333_, lean_object* v_x_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v_preNode_331_, v_postNode_332_, v_x_333_, v_x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_336_, lean_object* v_preNode_337_, lean_object* v_postNode_338_, lean_object* v___x_339_, lean_object* v_x_340_, lean_object* v_x_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4___redArg(v_preNode_337_, v_postNode_338_, v___x_339_, v_x_340_, v_x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0(lean_object* v_toPure_343_, lean_object* v_____do__lift_344_){
_start:
{
if (lean_obj_tag(v_____do__lift_344_) == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_box(0);
v___x_346_ = lean_apply_2(v_toPure_343_, lean_box(0), v___x_345_);
return v___x_346_;
}
else
{
lean_object* v_val_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_val_347_ = lean_ctor_get(v_____do__lift_344_, 0);
v___x_348_ = lean_box(0);
lean_inc(v_val_347_);
v___x_349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_349_, 0, v_val_347_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = lean_apply_2(v_toPure_343_, lean_box(0), v___x_349_);
return v___x_350_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0___boxed(lean_object* v_toPure_351_, lean_object* v_____do__lift_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0(v_toPure_351_, v_____do__lift_352_);
lean_dec(v_____do__lift_352_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__1(lean_object* v_toPure_354_, lean_object* v_p_355_, lean_object* v_toBind_356_, lean_object* v___f_357_, lean_object* v_ctx_358_, lean_object* v_i_359_, lean_object* v_cs_360_, lean_object* v_rs_361_){
_start:
{
uint8_t v___x_362_; 
v___x_362_ = l_List_isEmpty___redArg(v_rs_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
lean_dec_ref(v_cs_360_);
lean_dec_ref(v_i_359_);
lean_dec_ref(v_ctx_358_);
lean_dec(v___f_357_);
lean_dec(v_toBind_356_);
lean_dec(v_p_355_);
v___x_363_ = lean_apply_2(v_toPure_354_, lean_box(0), v_rs_361_);
return v___x_363_;
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec(v_rs_361_);
lean_dec(v_toPure_354_);
v___x_364_ = lean_apply_3(v_p_355_, v_ctx_358_, v_i_359_, v_cs_360_);
v___x_365_ = lean_apply_4(v_toBind_356_, lean_box(0), lean_box(0), v___x_364_, v___f_357_);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg(lean_object* v_inst_366_, lean_object* v_p_367_, lean_object* v_infoTree_368_){
_start:
{
lean_object* v_toApplicative_369_; lean_object* v_toBind_370_; lean_object* v_toPure_371_; lean_object* v___f_372_; lean_object* v___f_373_; lean_object* v___x_374_; 
v_toApplicative_369_ = lean_ctor_get(v_inst_366_, 0);
v_toBind_370_ = lean_ctor_get(v_inst_366_, 1);
v_toPure_371_ = lean_ctor_get(v_toApplicative_369_, 1);
lean_inc_n(v_toPure_371_, 2);
v___f_372_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_372_, 0, v_toPure_371_);
lean_inc(v_toBind_370_);
v___f_373_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__1), 8, 4);
lean_closure_set(v___f_373_, 0, v_toPure_371_);
lean_closure_set(v___f_373_, 1, v_p_367_);
lean_closure_set(v___f_373_, 2, v_toBind_370_);
lean_closure_set(v___f_373_, 3, v___f_372_);
v___x_374_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg(v_inst_366_, v___f_373_, v_infoTree_368_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM(lean_object* v_m_375_, lean_object* v_00_u03b1_376_, lean_object* v_inst_377_, lean_object* v_p_378_, lean_object* v_infoTree_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Elab_InfoTree_deepestNodesM___redArg(v_inst_377_, v_p_378_, v_infoTree_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodes___redArg___lam__0(lean_object* v_p_381_, lean_object* v_x1_382_, lean_object* v_x2_383_, lean_object* v_x3_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lean_apply_3(v_p_381_, v_x1_382_, v_x2_383_, v_x3_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0(lean_object* v_p_386_, lean_object* v_ctx_387_, lean_object* v_i_388_, lean_object* v_cs_389_, lean_object* v_rs_390_){
_start:
{
uint8_t v___x_391_; 
v___x_391_ = l_List_isEmpty___redArg(v_rs_390_);
if (v___x_391_ == 0)
{
lean_dec_ref(v_cs_389_);
lean_dec_ref(v_i_388_);
lean_dec_ref(v_ctx_387_);
lean_dec_ref(v_p_386_);
lean_inc(v_rs_390_);
return v_rs_390_;
}
else
{
lean_object* v___x_392_; 
v___x_392_ = lean_apply_3(v_p_386_, v_ctx_387_, v_i_388_, v_cs_389_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v___x_393_; 
v___x_393_ = lean_box(0);
return v___x_393_;
}
else
{
lean_object* v_val_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_val_394_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_val_394_);
lean_dec_ref_known(v___x_392_, 1);
v___x_395_ = lean_box(0);
v___x_396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_396_, 0, v_val_394_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
return v___x_396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0___boxed(lean_object* v_p_397_, lean_object* v_ctx_398_, lean_object* v_i_399_, lean_object* v_cs_400_, lean_object* v_rs_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0(v_p_397_, v_ctx_398_, v_i_399_, v_cs_400_, v_rs_401_);
lean_dec(v_rs_401_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg(lean_object* v_p_403_, lean_object* v_infoTree_404_){
_start:
{
lean_object* v___f_405_; lean_object* v___x_406_; 
v___f_405_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_405_, 0, v_p_403_);
v___x_406_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg(v___f_405_, v_infoTree_404_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodes___redArg(lean_object* v_p_407_, lean_object* v_infoTree_408_){
_start:
{
lean_object* v___f_409_; lean_object* v___x_410_; 
v___f_409_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_deepestNodes___redArg___lam__0), 4, 1);
lean_closure_set(v___f_409_, 0, v_p_407_);
v___x_410_ = l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg(v___f_409_, v_infoTree_408_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodes(lean_object* v_00_u03b1_411_, lean_object* v_p_412_, lean_object* v_infoTree_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v_p_412_, v_infoTree_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0(lean_object* v_00_u03b1_415_, lean_object* v_p_416_, lean_object* v_infoTree_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg(v_p_416_, v_infoTree_417_);
return v___x_418_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(lean_object* v_f_420_, lean_object* v___x_421_, lean_object* v_x_422_, lean_object* v_x_423_){
_start:
{
if (lean_obj_tag(v_x_422_) == 0)
{
lean_object* v_cs_424_; lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v_cs_424_ = lean_ctor_get(v_x_422_, 0);
v___x_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = lean_array_get_size(v_cs_424_);
v___x_427_ = lean_nat_dec_lt(v___x_425_, v___x_426_);
if (v___x_427_ == 0)
{
lean_dec(v___x_421_);
lean_dec(v_f_420_);
return v_x_423_;
}
else
{
size_t v___x_428_; size_t v___x_429_; lean_object* v___x_430_; 
v___x_428_ = ((size_t)0ULL);
v___x_429_ = lean_usize_of_nat(v___x_426_);
v___x_430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_420_, v___x_421_, v_cs_424_, v___x_428_, v___x_429_, v_x_423_);
return v___x_430_;
}
}
else
{
lean_object* v_vs_431_; lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v_vs_431_ = lean_ctor_get(v_x_422_, 0);
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = lean_array_get_size(v_vs_431_);
v___x_434_ = lean_nat_dec_lt(v___x_432_, v___x_433_);
if (v___x_434_ == 0)
{
lean_dec(v___x_421_);
lean_dec(v_f_420_);
return v_x_423_;
}
else
{
size_t v___x_435_; size_t v___x_436_; lean_object* v___x_437_; 
v___x_435_ = ((size_t)0ULL);
v___x_436_ = lean_usize_of_nat(v___x_433_);
v___x_437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_420_, v___x_421_, v_vs_431_, v___x_435_, v___x_436_, v_x_423_);
return v___x_437_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(lean_object* v_f_438_, lean_object* v___x_439_, lean_object* v_as_440_, size_t v_i_441_, size_t v_stop_442_, lean_object* v_b_443_){
_start:
{
uint8_t v___x_444_; 
v___x_444_ = lean_usize_dec_eq(v_i_441_, v_stop_442_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; size_t v___x_447_; size_t v___x_448_; 
v___x_445_ = lean_array_uget_borrowed(v_as_440_, v_i_441_);
lean_inc(v___x_439_);
lean_inc(v_f_438_);
v___x_446_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(v_f_438_, v___x_439_, v___x_445_, v_b_443_);
v___x_447_ = ((size_t)1ULL);
v___x_448_ = lean_usize_add(v_i_441_, v___x_447_);
v_i_441_ = v___x_448_;
v_b_443_ = v___x_446_;
goto _start;
}
else
{
lean_dec(v___x_439_);
lean_dec(v_f_438_);
return v_b_443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(lean_object* v_f_450_, lean_object* v___x_451_, lean_object* v_x_452_, size_t v_x_453_, size_t v_x_454_, lean_object* v_x_455_){
_start:
{
if (lean_obj_tag(v_x_452_) == 0)
{
lean_object* v_cs_456_; lean_object* v___x_457_; size_t v___x_458_; lean_object* v_j_459_; lean_object* v___x_460_; size_t v___x_461_; size_t v___x_462_; size_t v___x_463_; size_t v___x_464_; size_t v___x_465_; size_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v_cs_456_ = lean_ctor_get(v_x_452_, 0);
v___x_457_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0);
v___x_458_ = lean_usize_shift_right(v_x_453_, v_x_454_);
v_j_459_ = lean_usize_to_nat(v___x_458_);
v___x_460_ = lean_array_get_borrowed(v___x_457_, v_cs_456_, v_j_459_);
v___x_461_ = ((size_t)1ULL);
v___x_462_ = lean_usize_shift_left(v___x_461_, v_x_454_);
v___x_463_ = lean_usize_sub(v___x_462_, v___x_461_);
v___x_464_ = lean_usize_land(v_x_453_, v___x_463_);
v___x_465_ = ((size_t)5ULL);
v___x_466_ = lean_usize_sub(v_x_454_, v___x_465_);
lean_inc(v___x_451_);
lean_inc(v_f_450_);
v___x_467_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(v_f_450_, v___x_451_, v___x_460_, v___x_464_, v___x_466_, v_x_455_);
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = lean_nat_add(v_j_459_, v___x_468_);
lean_dec(v_j_459_);
v___x_470_ = lean_array_get_size(v_cs_456_);
v___x_471_ = lean_nat_dec_lt(v___x_469_, v___x_470_);
if (v___x_471_ == 0)
{
lean_dec(v___x_469_);
lean_dec(v___x_451_);
lean_dec(v_f_450_);
return v___x_467_;
}
else
{
size_t v___x_472_; size_t v___x_473_; lean_object* v___x_474_; 
v___x_472_ = lean_usize_of_nat(v___x_469_);
lean_dec(v___x_469_);
v___x_473_ = lean_usize_of_nat(v___x_470_);
v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_450_, v___x_451_, v_cs_456_, v___x_472_, v___x_473_, v___x_467_);
return v___x_474_;
}
}
else
{
lean_object* v_vs_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v_vs_475_ = lean_ctor_get(v_x_452_, 0);
v___x_476_ = lean_usize_to_nat(v_x_453_);
v___x_477_ = lean_array_get_size(v_vs_475_);
v___x_478_ = lean_nat_dec_lt(v___x_476_, v___x_477_);
if (v___x_478_ == 0)
{
lean_dec(v___x_476_);
lean_dec(v___x_451_);
lean_dec(v_f_450_);
return v_x_455_;
}
else
{
size_t v___x_479_; size_t v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_usize_of_nat(v___x_476_);
lean_dec(v___x_476_);
v___x_480_ = lean_usize_of_nat(v___x_477_);
v___x_481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_450_, v___x_451_, v_vs_475_, v___x_479_, v___x_480_, v_x_455_);
return v___x_481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(lean_object* v_f_482_, lean_object* v___x_483_, lean_object* v_t_484_, lean_object* v_init_485_, lean_object* v_start_486_){
_start:
{
lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = lean_nat_dec_eq(v_start_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v_root_489_; lean_object* v_tail_490_; size_t v_shift_491_; lean_object* v_tailOff_492_; uint8_t v___x_493_; 
v_root_489_ = lean_ctor_get(v_t_484_, 0);
v_tail_490_ = lean_ctor_get(v_t_484_, 1);
v_shift_491_ = lean_ctor_get_usize(v_t_484_, 4);
v_tailOff_492_ = lean_ctor_get(v_t_484_, 3);
v___x_493_ = lean_nat_dec_le(v_tailOff_492_, v_start_486_);
if (v___x_493_ == 0)
{
size_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_494_ = lean_usize_of_nat(v_start_486_);
lean_inc(v___x_483_);
lean_inc(v_f_482_);
v___x_495_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(v_f_482_, v___x_483_, v_root_489_, v___x_494_, v_shift_491_, v_init_485_);
v___x_496_ = lean_array_get_size(v_tail_490_);
v___x_497_ = lean_nat_dec_lt(v___x_487_, v___x_496_);
if (v___x_497_ == 0)
{
lean_dec(v___x_483_);
lean_dec(v_f_482_);
return v___x_495_;
}
else
{
size_t v___x_498_; size_t v___x_499_; lean_object* v___x_500_; 
v___x_498_ = ((size_t)0ULL);
v___x_499_ = lean_usize_of_nat(v___x_496_);
v___x_500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_482_, v___x_483_, v_tail_490_, v___x_498_, v___x_499_, v___x_495_);
return v___x_500_;
}
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_501_ = lean_nat_sub(v_start_486_, v_tailOff_492_);
v___x_502_ = lean_array_get_size(v_tail_490_);
v___x_503_ = lean_nat_dec_lt(v___x_501_, v___x_502_);
if (v___x_503_ == 0)
{
lean_dec(v___x_501_);
lean_dec(v___x_483_);
lean_dec(v_f_482_);
return v_init_485_;
}
else
{
size_t v___x_504_; size_t v___x_505_; lean_object* v___x_506_; 
v___x_504_ = lean_usize_of_nat(v___x_501_);
lean_dec(v___x_501_);
v___x_505_ = lean_usize_of_nat(v___x_502_);
v___x_506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_482_, v___x_483_, v_tail_490_, v___x_504_, v___x_505_, v_init_485_);
return v___x_506_;
}
}
}
else
{
lean_object* v_root_507_; lean_object* v_tail_508_; lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v_root_507_ = lean_ctor_get(v_t_484_, 0);
v_tail_508_ = lean_ctor_get(v_t_484_, 1);
lean_inc(v___x_483_);
lean_inc(v_f_482_);
v___x_509_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(v_f_482_, v___x_483_, v_root_507_, v_init_485_);
v___x_510_ = lean_array_get_size(v_tail_508_);
v___x_511_ = lean_nat_dec_lt(v___x_487_, v___x_510_);
if (v___x_511_ == 0)
{
lean_dec(v___x_483_);
lean_dec(v_f_482_);
return v___x_509_;
}
else
{
size_t v___x_512_; size_t v___x_513_; lean_object* v___x_514_; 
v___x_512_ = ((size_t)0ULL);
v___x_513_ = lean_usize_of_nat(v___x_510_);
v___x_514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_482_, v___x_483_, v_tail_508_, v___x_512_, v___x_513_, v___x_509_);
return v___x_514_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go___redArg(lean_object* v_f_515_, lean_object* v_ctx_x3f_516_, lean_object* v_a_517_, lean_object* v_x_518_){
_start:
{
switch(lean_obj_tag(v_x_518_))
{
case 0:
{
lean_object* v_i_519_; lean_object* v_t_520_; lean_object* v___x_521_; 
v_i_519_ = lean_ctor_get(v_x_518_, 0);
lean_inc_ref(v_i_519_);
v_t_520_ = lean_ctor_get(v_x_518_, 1);
lean_inc_ref(v_t_520_);
lean_dec_ref_known(v_x_518_, 2);
v___x_521_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_519_, v_ctx_x3f_516_);
v_ctx_x3f_516_ = v___x_521_;
v_x_518_ = v_t_520_;
goto _start;
}
case 1:
{
lean_object* v_i_523_; lean_object* v_children_524_; lean_object* v___y_526_; 
v_i_523_ = lean_ctor_get(v_x_518_, 0);
lean_inc_ref(v_i_523_);
v_children_524_ = lean_ctor_get(v_x_518_, 1);
lean_inc_ref(v_children_524_);
lean_dec_ref_known(v_x_518_, 2);
if (lean_obj_tag(v_ctx_x3f_516_) == 0)
{
v___y_526_ = v_a_517_;
goto v___jp_525_;
}
else
{
lean_object* v_val_530_; lean_object* v___x_531_; 
v_val_530_ = lean_ctor_get(v_ctx_x3f_516_, 0);
lean_inc(v_f_515_);
lean_inc_ref(v_i_523_);
lean_inc(v_val_530_);
v___x_531_ = lean_apply_3(v_f_515_, v_val_530_, v_i_523_, v_a_517_);
v___y_526_ = v___x_531_;
goto v___jp_525_;
}
v___jp_525_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_527_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_516_, v_i_523_);
lean_dec_ref(v_i_523_);
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(v_f_515_, v___x_527_, v_children_524_, v___y_526_, v___x_528_);
lean_dec_ref(v_children_524_);
return v___x_529_;
}
}
default: 
{
lean_dec_ref_known(v_x_518_, 1);
lean_dec(v_ctx_x3f_516_);
lean_dec(v_f_515_);
return v_a_517_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(lean_object* v_f_532_, lean_object* v___x_533_, lean_object* v_as_534_, size_t v_i_535_, size_t v_stop_536_, lean_object* v_b_537_){
_start:
{
uint8_t v___x_538_; 
v___x_538_ = lean_usize_dec_eq(v_i_535_, v_stop_536_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; size_t v___x_541_; size_t v___x_542_; 
v___x_539_ = lean_array_uget_borrowed(v_as_534_, v_i_535_);
lean_inc(v___x_539_);
lean_inc(v___x_533_);
lean_inc(v_f_532_);
v___x_540_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go___redArg(v_f_532_, v___x_533_, v_b_537_, v___x_539_);
v___x_541_ = ((size_t)1ULL);
v___x_542_ = lean_usize_add(v_i_535_, v___x_541_);
v_i_535_ = v___x_542_;
v_b_537_ = v___x_540_;
goto _start;
}
else
{
lean_dec(v___x_533_);
lean_dec(v_f_532_);
return v_b_537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg___boxed(lean_object* v_f_544_, lean_object* v___x_545_, lean_object* v_as_546_, lean_object* v_i_547_, lean_object* v_stop_548_, lean_object* v_b_549_){
_start:
{
size_t v_i_boxed_550_; size_t v_stop_boxed_551_; lean_object* v_res_552_; 
v_i_boxed_550_ = lean_unbox_usize(v_i_547_);
lean_dec(v_i_547_);
v_stop_boxed_551_ = lean_unbox_usize(v_stop_548_);
lean_dec(v_stop_548_);
v_res_552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_544_, v___x_545_, v_as_546_, v_i_boxed_550_, v_stop_boxed_551_, v_b_549_);
lean_dec_ref(v_as_546_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_553_, lean_object* v___x_554_, lean_object* v_as_555_, lean_object* v_i_556_, lean_object* v_stop_557_, lean_object* v_b_558_){
_start:
{
size_t v_i_boxed_559_; size_t v_stop_boxed_560_; lean_object* v_res_561_; 
v_i_boxed_559_ = lean_unbox_usize(v_i_556_);
lean_dec(v_i_556_);
v_stop_boxed_560_ = lean_unbox_usize(v_stop_557_);
lean_dec(v_stop_557_);
v_res_561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_553_, v___x_554_, v_as_555_, v_i_boxed_559_, v_stop_boxed_560_, v_b_558_);
lean_dec_ref(v_as_555_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg___boxed(lean_object* v_f_562_, lean_object* v___x_563_, lean_object* v_x_564_, lean_object* v_x_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(v_f_562_, v___x_563_, v_x_564_, v_x_565_);
lean_dec_ref(v_x_564_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___boxed(lean_object* v_f_567_, lean_object* v___x_568_, lean_object* v_x_569_, lean_object* v_x_570_, lean_object* v_x_571_, lean_object* v_x_572_){
_start:
{
size_t v_x_1172__boxed_573_; size_t v_x_1173__boxed_574_; lean_object* v_res_575_; 
v_x_1172__boxed_573_ = lean_unbox_usize(v_x_570_);
lean_dec(v_x_570_);
v_x_1173__boxed_574_ = lean_unbox_usize(v_x_571_);
lean_dec(v_x_571_);
v_res_575_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(v_f_567_, v___x_568_, v_x_569_, v_x_1172__boxed_573_, v_x_1173__boxed_574_, v_x_572_);
lean_dec_ref(v_x_569_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg___boxed(lean_object* v_f_576_, lean_object* v___x_577_, lean_object* v_t_578_, lean_object* v_init_579_, lean_object* v_start_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(v_f_576_, v___x_577_, v_t_578_, v_init_579_, v_start_580_);
lean_dec(v_start_580_);
lean_dec_ref(v_t_578_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go(lean_object* v_00_u03b1_582_, lean_object* v_f_583_, lean_object* v_ctx_x3f_584_, lean_object* v_a_585_, lean_object* v_x_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go___redArg(v_f_583_, v_ctx_x3f_584_, v_a_585_, v_x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0(lean_object* v_00_u03b1_588_, lean_object* v_f_589_, lean_object* v___x_590_, lean_object* v_t_591_, lean_object* v_init_592_, lean_object* v_start_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(v_f_589_, v___x_590_, v_t_591_, v_init_592_, v_start_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___boxed(lean_object* v_00_u03b1_595_, lean_object* v_f_596_, lean_object* v___x_597_, lean_object* v_t_598_, lean_object* v_init_599_, lean_object* v_start_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0(v_00_u03b1_595_, v_f_596_, v___x_597_, v_t_598_, v_init_599_, v_start_600_);
lean_dec(v_start_600_);
lean_dec_ref(v_t_598_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0(lean_object* v_00_u03b1_602_, lean_object* v_f_603_, lean_object* v___x_604_, lean_object* v_x_605_, size_t v_x_606_, size_t v_x_607_, lean_object* v_x_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(v_f_603_, v___x_604_, v_x_605_, v_x_606_, v_x_607_, v_x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_610_, lean_object* v_f_611_, lean_object* v___x_612_, lean_object* v_x_613_, lean_object* v_x_614_, lean_object* v_x_615_, lean_object* v_x_616_){
_start:
{
size_t v_x_1344__boxed_617_; size_t v_x_1345__boxed_618_; lean_object* v_res_619_; 
v_x_1344__boxed_617_ = lean_unbox_usize(v_x_614_);
lean_dec(v_x_614_);
v_x_1345__boxed_618_ = lean_unbox_usize(v_x_615_);
lean_dec(v_x_615_);
v_res_619_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0(v_00_u03b1_610_, v_f_611_, v___x_612_, v_x_613_, v_x_1344__boxed_617_, v_x_1345__boxed_618_, v_x_616_);
lean_dec_ref(v_x_613_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1(lean_object* v_00_u03b1_620_, lean_object* v_f_621_, lean_object* v___x_622_, lean_object* v_as_623_, size_t v_i_624_, size_t v_stop_625_, lean_object* v_b_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_621_, v___x_622_, v_as_623_, v_i_624_, v_stop_625_, v_b_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___boxed(lean_object* v_00_u03b1_628_, lean_object* v_f_629_, lean_object* v___x_630_, lean_object* v_as_631_, lean_object* v_i_632_, lean_object* v_stop_633_, lean_object* v_b_634_){
_start:
{
size_t v_i_boxed_635_; size_t v_stop_boxed_636_; lean_object* v_res_637_; 
v_i_boxed_635_ = lean_unbox_usize(v_i_632_);
lean_dec(v_i_632_);
v_stop_boxed_636_ = lean_unbox_usize(v_stop_633_);
lean_dec(v_stop_633_);
v_res_637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1(v_00_u03b1_628_, v_f_629_, v___x_630_, v_as_631_, v_i_boxed_635_, v_stop_boxed_636_, v_b_634_);
lean_dec_ref(v_as_631_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2(lean_object* v_00_u03b1_638_, lean_object* v_f_639_, lean_object* v___x_640_, lean_object* v_x_641_, lean_object* v_x_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(v_f_639_, v___x_640_, v_x_641_, v_x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___boxed(lean_object* v_00_u03b1_644_, lean_object* v_f_645_, lean_object* v___x_646_, lean_object* v_x_647_, lean_object* v_x_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2(v_00_u03b1_644_, v_f_645_, v___x_646_, v_x_647_, v_x_648_);
lean_dec_ref(v_x_647_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_650_, lean_object* v_f_651_, lean_object* v___x_652_, lean_object* v_as_653_, size_t v_i_654_, size_t v_stop_655_, lean_object* v_b_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_651_, v___x_652_, v_as_653_, v_i_654_, v_stop_655_, v_b_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_658_, lean_object* v_f_659_, lean_object* v___x_660_, lean_object* v_as_661_, lean_object* v_i_662_, lean_object* v_stop_663_, lean_object* v_b_664_){
_start:
{
size_t v_i_boxed_665_; size_t v_stop_boxed_666_; lean_object* v_res_667_; 
v_i_boxed_665_ = lean_unbox_usize(v_i_662_);
lean_dec(v_i_662_);
v_stop_boxed_666_ = lean_unbox_usize(v_stop_663_);
lean_dec(v_stop_663_);
v_res_667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1(v_00_u03b1_658_, v_f_659_, v___x_660_, v_as_661_, v_i_boxed_665_, v_stop_boxed_666_, v_b_664_);
lean_dec_ref(v_as_661_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfo___redArg(lean_object* v_f_668_, lean_object* v_init_669_, lean_object* v_x_670_){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_box(0);
v___x_672_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go___redArg(v_f_668_, v___x_671_, v_init_669_, v_x_670_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfo(lean_object* v_00_u03b1_673_, lean_object* v_f_674_, lean_object* v_init_675_, lean_object* v_x_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v_f_674_, v_init_675_, v_x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__1(lean_object* v___f_678_, lean_object* v_a_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = lean_apply_1(v___f_678_, v_a_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0___boxed(lean_object* v_ctx_x3f_681_, lean_object* v_i_682_, lean_object* v_inst_683_, lean_object* v_f_684_, lean_object* v_children_685_, lean_object* v_a_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0(v_ctx_x3f_681_, v_i_682_, v_inst_683_, v_f_684_, v_children_685_, v_a_686_);
lean_dec_ref(v_i_682_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg(lean_object* v_inst_688_, lean_object* v_f_689_, lean_object* v_ctx_x3f_690_, lean_object* v_a_691_, lean_object* v_x_692_){
_start:
{
switch(lean_obj_tag(v_x_692_))
{
case 0:
{
lean_object* v_i_693_; lean_object* v_t_694_; lean_object* v___x_695_; 
v_i_693_ = lean_ctor_get(v_x_692_, 0);
lean_inc_ref(v_i_693_);
v_t_694_ = lean_ctor_get(v_x_692_, 1);
lean_inc_ref(v_t_694_);
lean_dec_ref_known(v_x_692_, 2);
v___x_695_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_693_, v_ctx_x3f_690_);
v_ctx_x3f_690_ = v___x_695_;
v_x_692_ = v_t_694_;
goto _start;
}
case 1:
{
lean_object* v_toApplicative_697_; lean_object* v_toBind_698_; lean_object* v_toPure_699_; lean_object* v_i_700_; lean_object* v_children_701_; lean_object* v___f_702_; 
v_toApplicative_697_ = lean_ctor_get(v_inst_688_, 0);
v_toBind_698_ = lean_ctor_get(v_inst_688_, 1);
lean_inc(v_toBind_698_);
v_toPure_699_ = lean_ctor_get(v_toApplicative_697_, 1);
lean_inc(v_toPure_699_);
v_i_700_ = lean_ctor_get(v_x_692_, 0);
lean_inc_ref_n(v_i_700_, 2);
v_children_701_ = lean_ctor_get(v_x_692_, 1);
lean_inc_ref(v_children_701_);
lean_dec_ref_known(v_x_692_, 2);
lean_inc(v_f_689_);
lean_inc(v_ctx_x3f_690_);
v___f_702_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_702_, 0, v_ctx_x3f_690_);
lean_closure_set(v___f_702_, 1, v_i_700_);
lean_closure_set(v___f_702_, 2, v_inst_688_);
lean_closure_set(v___f_702_, 3, v_f_689_);
lean_closure_set(v___f_702_, 4, v_children_701_);
if (lean_obj_tag(v_ctx_x3f_690_) == 0)
{
lean_object* v___f_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
lean_dec_ref(v_i_700_);
lean_dec(v_f_689_);
v___f_703_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__1), 2, 1);
lean_closure_set(v___f_703_, 0, v___f_702_);
v___x_704_ = lean_apply_2(v_toPure_699_, lean_box(0), v_a_691_);
v___x_705_ = lean_apply_4(v_toBind_698_, lean_box(0), lean_box(0), v___x_704_, v___f_703_);
return v___x_705_;
}
else
{
lean_object* v_val_706_; lean_object* v___f_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
lean_dec(v_toPure_699_);
v_val_706_ = lean_ctor_get(v_ctx_x3f_690_, 0);
lean_inc(v_val_706_);
lean_dec_ref_known(v_ctx_x3f_690_, 1);
v___f_707_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__1), 2, 1);
lean_closure_set(v___f_707_, 0, v___f_702_);
v___x_708_ = lean_apply_3(v_f_689_, v_val_706_, v_i_700_, v_a_691_);
v___x_709_ = lean_apply_4(v_toBind_698_, lean_box(0), lean_box(0), v___x_708_, v___f_707_);
return v___x_709_;
}
}
default: 
{
lean_object* v_toApplicative_710_; lean_object* v_toPure_711_; lean_object* v___x_712_; 
v_toApplicative_710_ = lean_ctor_get(v_inst_688_, 0);
lean_inc_ref(v_toApplicative_710_);
lean_dec_ref_known(v_x_692_, 1);
lean_dec(v_ctx_x3f_690_);
lean_dec(v_f_689_);
lean_dec_ref(v_inst_688_);
v_toPure_711_ = lean_ctor_get(v_toApplicative_710_, 1);
lean_inc(v_toPure_711_);
lean_dec_ref(v_toApplicative_710_);
v___x_712_ = lean_apply_2(v_toPure_711_, lean_box(0), v_a_691_);
return v___x_712_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0(lean_object* v_ctx_x3f_713_, lean_object* v_i_714_, lean_object* v_inst_715_, lean_object* v_f_716_, lean_object* v_children_717_, lean_object* v_a_718_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_719_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_713_, v_i_714_);
lean_inc_ref(v_inst_715_);
v___x_720_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg), 5, 3);
lean_closure_set(v___x_720_, 0, v_inst_715_);
lean_closure_set(v___x_720_, 1, v_f_716_);
lean_closure_set(v___x_720_, 2, v___x_719_);
v___x_721_ = lean_unsigned_to_nat(0u);
v___x_722_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_715_, v_children_717_, v___x_720_, v_a_718_, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go(lean_object* v_m_723_, lean_object* v_00_u03b1_724_, lean_object* v_inst_725_, lean_object* v_f_726_, lean_object* v_ctx_x3f_727_, lean_object* v_a_728_, lean_object* v_x_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg(v_inst_725_, v_f_726_, v_ctx_x3f_727_, v_a_728_, v_x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___redArg(lean_object* v_inst_731_, lean_object* v_f_732_, lean_object* v_init_733_, lean_object* v_x_734_){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_box(0);
v___x_736_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg(v_inst_731_, v_f_732_, v___x_735_, v_init_733_, v_x_734_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM(lean_object* v_m_737_, lean_object* v_00_u03b1_738_, lean_object* v_inst_739_, lean_object* v_f_740_, lean_object* v_init_741_, lean_object* v_x_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Elab_InfoTree_foldInfoM___redArg(v_inst_739_, v_f_740_, v_init_741_, v_x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(lean_object* v_f_744_, lean_object* v___x_745_, lean_object* v_x_746_, lean_object* v_x_747_){
_start:
{
if (lean_obj_tag(v_x_746_) == 0)
{
lean_object* v_cs_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v_cs_748_ = lean_ctor_get(v_x_746_, 0);
v___x_749_ = lean_unsigned_to_nat(0u);
v___x_750_ = lean_array_get_size(v_cs_748_);
v___x_751_ = lean_nat_dec_lt(v___x_749_, v___x_750_);
if (v___x_751_ == 0)
{
lean_dec(v___x_745_);
lean_dec(v_f_744_);
return v_x_747_;
}
else
{
size_t v___x_752_; size_t v___x_753_; lean_object* v___x_754_; 
v___x_752_ = ((size_t)0ULL);
v___x_753_ = lean_usize_of_nat(v___x_750_);
v___x_754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_744_, v___x_745_, v_cs_748_, v___x_752_, v___x_753_, v_x_747_);
return v___x_754_;
}
}
else
{
lean_object* v_vs_755_; lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v_vs_755_ = lean_ctor_get(v_x_746_, 0);
v___x_756_ = lean_unsigned_to_nat(0u);
v___x_757_ = lean_array_get_size(v_vs_755_);
v___x_758_ = lean_nat_dec_lt(v___x_756_, v___x_757_);
if (v___x_758_ == 0)
{
lean_dec(v___x_745_);
lean_dec(v_f_744_);
return v_x_747_;
}
else
{
size_t v___x_759_; size_t v___x_760_; lean_object* v___x_761_; 
v___x_759_ = ((size_t)0ULL);
v___x_760_ = lean_usize_of_nat(v___x_757_);
v___x_761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_744_, v___x_745_, v_vs_755_, v___x_759_, v___x_760_, v_x_747_);
return v___x_761_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(lean_object* v_f_762_, lean_object* v___x_763_, lean_object* v_as_764_, size_t v_i_765_, size_t v_stop_766_, lean_object* v_b_767_){
_start:
{
uint8_t v___x_768_; 
v___x_768_ = lean_usize_dec_eq(v_i_765_, v_stop_766_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; size_t v___x_771_; size_t v___x_772_; 
v___x_769_ = lean_array_uget_borrowed(v_as_764_, v_i_765_);
lean_inc(v___x_763_);
lean_inc(v_f_762_);
v___x_770_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(v_f_762_, v___x_763_, v___x_769_, v_b_767_);
v___x_771_ = ((size_t)1ULL);
v___x_772_ = lean_usize_add(v_i_765_, v___x_771_);
v_i_765_ = v___x_772_;
v_b_767_ = v___x_770_;
goto _start;
}
else
{
lean_dec(v___x_763_);
lean_dec(v_f_762_);
return v_b_767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(lean_object* v_f_774_, lean_object* v___x_775_, lean_object* v_x_776_, size_t v_x_777_, size_t v_x_778_, lean_object* v_x_779_){
_start:
{
if (lean_obj_tag(v_x_776_) == 0)
{
lean_object* v_cs_780_; lean_object* v___x_781_; size_t v___x_782_; lean_object* v_j_783_; lean_object* v___x_784_; size_t v___x_785_; size_t v___x_786_; size_t v___x_787_; size_t v___x_788_; size_t v___x_789_; size_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v_cs_780_ = lean_ctor_get(v_x_776_, 0);
v___x_781_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0);
v___x_782_ = lean_usize_shift_right(v_x_777_, v_x_778_);
v_j_783_ = lean_usize_to_nat(v___x_782_);
v___x_784_ = lean_array_get_borrowed(v___x_781_, v_cs_780_, v_j_783_);
v___x_785_ = ((size_t)1ULL);
v___x_786_ = lean_usize_shift_left(v___x_785_, v_x_778_);
v___x_787_ = lean_usize_sub(v___x_786_, v___x_785_);
v___x_788_ = lean_usize_land(v_x_777_, v___x_787_);
v___x_789_ = ((size_t)5ULL);
v___x_790_ = lean_usize_sub(v_x_778_, v___x_789_);
lean_inc(v___x_775_);
lean_inc(v_f_774_);
v___x_791_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(v_f_774_, v___x_775_, v___x_784_, v___x_788_, v___x_790_, v_x_779_);
v___x_792_ = lean_unsigned_to_nat(1u);
v___x_793_ = lean_nat_add(v_j_783_, v___x_792_);
lean_dec(v_j_783_);
v___x_794_ = lean_array_get_size(v_cs_780_);
v___x_795_ = lean_nat_dec_lt(v___x_793_, v___x_794_);
if (v___x_795_ == 0)
{
lean_dec(v___x_793_);
lean_dec(v___x_775_);
lean_dec(v_f_774_);
return v___x_791_;
}
else
{
size_t v___x_796_; size_t v___x_797_; lean_object* v___x_798_; 
v___x_796_ = lean_usize_of_nat(v___x_793_);
lean_dec(v___x_793_);
v___x_797_ = lean_usize_of_nat(v___x_794_);
v___x_798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_774_, v___x_775_, v_cs_780_, v___x_796_, v___x_797_, v___x_791_);
return v___x_798_;
}
}
else
{
lean_object* v_vs_799_; lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v_vs_799_ = lean_ctor_get(v_x_776_, 0);
v___x_800_ = lean_usize_to_nat(v_x_777_);
v___x_801_ = lean_array_get_size(v_vs_799_);
v___x_802_ = lean_nat_dec_lt(v___x_800_, v___x_801_);
if (v___x_802_ == 0)
{
lean_dec(v___x_800_);
lean_dec(v___x_775_);
lean_dec(v_f_774_);
return v_x_779_;
}
else
{
size_t v___x_803_; size_t v___x_804_; lean_object* v___x_805_; 
v___x_803_ = lean_usize_of_nat(v___x_800_);
lean_dec(v___x_800_);
v___x_804_ = lean_usize_of_nat(v___x_801_);
v___x_805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_774_, v___x_775_, v_vs_799_, v___x_803_, v___x_804_, v_x_779_);
return v___x_805_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(lean_object* v_f_806_, lean_object* v___x_807_, lean_object* v_t_808_, lean_object* v_init_809_, lean_object* v_start_810_){
_start:
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = lean_unsigned_to_nat(0u);
v___x_812_ = lean_nat_dec_eq(v_start_810_, v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v_root_813_; lean_object* v_tail_814_; size_t v_shift_815_; lean_object* v_tailOff_816_; uint8_t v___x_817_; 
v_root_813_ = lean_ctor_get(v_t_808_, 0);
v_tail_814_ = lean_ctor_get(v_t_808_, 1);
v_shift_815_ = lean_ctor_get_usize(v_t_808_, 4);
v_tailOff_816_ = lean_ctor_get(v_t_808_, 3);
v___x_817_ = lean_nat_dec_le(v_tailOff_816_, v_start_810_);
if (v___x_817_ == 0)
{
size_t v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_818_ = lean_usize_of_nat(v_start_810_);
lean_inc(v___x_807_);
lean_inc(v_f_806_);
v___x_819_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(v_f_806_, v___x_807_, v_root_813_, v___x_818_, v_shift_815_, v_init_809_);
v___x_820_ = lean_array_get_size(v_tail_814_);
v___x_821_ = lean_nat_dec_lt(v___x_811_, v___x_820_);
if (v___x_821_ == 0)
{
lean_dec(v___x_807_);
lean_dec(v_f_806_);
return v___x_819_;
}
else
{
size_t v___x_822_; size_t v___x_823_; lean_object* v___x_824_; 
v___x_822_ = ((size_t)0ULL);
v___x_823_ = lean_usize_of_nat(v___x_820_);
v___x_824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_806_, v___x_807_, v_tail_814_, v___x_822_, v___x_823_, v___x_819_);
return v___x_824_;
}
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_825_ = lean_nat_sub(v_start_810_, v_tailOff_816_);
v___x_826_ = lean_array_get_size(v_tail_814_);
v___x_827_ = lean_nat_dec_lt(v___x_825_, v___x_826_);
if (v___x_827_ == 0)
{
lean_dec(v___x_825_);
lean_dec(v___x_807_);
lean_dec(v_f_806_);
return v_init_809_;
}
else
{
size_t v___x_828_; size_t v___x_829_; lean_object* v___x_830_; 
v___x_828_ = lean_usize_of_nat(v___x_825_);
lean_dec(v___x_825_);
v___x_829_ = lean_usize_of_nat(v___x_826_);
v___x_830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_806_, v___x_807_, v_tail_814_, v___x_828_, v___x_829_, v_init_809_);
return v___x_830_;
}
}
}
else
{
lean_object* v_root_831_; lean_object* v_tail_832_; lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v_root_831_ = lean_ctor_get(v_t_808_, 0);
v_tail_832_ = lean_ctor_get(v_t_808_, 1);
lean_inc(v___x_807_);
lean_inc(v_f_806_);
v___x_833_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(v_f_806_, v___x_807_, v_root_831_, v_init_809_);
v___x_834_ = lean_array_get_size(v_tail_832_);
v___x_835_ = lean_nat_dec_lt(v___x_811_, v___x_834_);
if (v___x_835_ == 0)
{
lean_dec(v___x_807_);
lean_dec(v_f_806_);
return v___x_833_;
}
else
{
size_t v___x_836_; size_t v___x_837_; lean_object* v___x_838_; 
v___x_836_ = ((size_t)0ULL);
v___x_837_ = lean_usize_of_nat(v___x_834_);
v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_806_, v___x_807_, v_tail_832_, v___x_836_, v___x_837_, v___x_833_);
return v___x_838_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(lean_object* v_f_839_, lean_object* v_ctx_x3f_840_, lean_object* v_a_841_, lean_object* v_x_842_){
_start:
{
switch(lean_obj_tag(v_x_842_))
{
case 0:
{
lean_object* v_i_843_; lean_object* v_t_844_; lean_object* v___x_845_; 
v_i_843_ = lean_ctor_get(v_x_842_, 0);
lean_inc_ref(v_i_843_);
v_t_844_ = lean_ctor_get(v_x_842_, 1);
lean_inc_ref(v_t_844_);
lean_dec_ref_known(v_x_842_, 2);
v___x_845_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_843_, v_ctx_x3f_840_);
v_ctx_x3f_840_ = v___x_845_;
v_x_842_ = v_t_844_;
goto _start;
}
case 1:
{
lean_object* v_i_847_; lean_object* v_children_848_; lean_object* v___y_850_; 
v_i_847_ = lean_ctor_get(v_x_842_, 0);
lean_inc_ref(v_i_847_);
v_children_848_ = lean_ctor_get(v_x_842_, 1);
lean_inc_ref(v_children_848_);
if (lean_obj_tag(v_ctx_x3f_840_) == 0)
{
lean_dec_ref_known(v_x_842_, 2);
v___y_850_ = v_a_841_;
goto v___jp_849_;
}
else
{
lean_object* v_val_854_; lean_object* v___x_855_; 
v_val_854_ = lean_ctor_get(v_ctx_x3f_840_, 0);
lean_inc(v_f_839_);
lean_inc(v_val_854_);
v___x_855_ = lean_apply_3(v_f_839_, v_val_854_, v_x_842_, v_a_841_);
v___y_850_ = v___x_855_;
goto v___jp_849_;
}
v___jp_849_:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_840_, v_i_847_);
lean_dec_ref(v_i_847_);
v___x_852_ = lean_unsigned_to_nat(0u);
v___x_853_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(v_f_839_, v___x_851_, v_children_848_, v___y_850_, v___x_852_);
lean_dec_ref(v_children_848_);
return v___x_853_;
}
}
default: 
{
lean_dec_ref_known(v_x_842_, 1);
lean_dec(v_ctx_x3f_840_);
lean_dec(v_f_839_);
return v_a_841_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(lean_object* v_f_856_, lean_object* v___x_857_, lean_object* v_as_858_, size_t v_i_859_, size_t v_stop_860_, lean_object* v_b_861_){
_start:
{
uint8_t v___x_862_; 
v___x_862_ = lean_usize_dec_eq(v_i_859_, v_stop_860_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; lean_object* v___x_864_; size_t v___x_865_; size_t v___x_866_; 
v___x_863_ = lean_array_uget_borrowed(v_as_858_, v_i_859_);
lean_inc(v___x_863_);
lean_inc(v___x_857_);
lean_inc(v_f_856_);
v___x_864_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(v_f_856_, v___x_857_, v_b_861_, v___x_863_);
v___x_865_ = ((size_t)1ULL);
v___x_866_ = lean_usize_add(v_i_859_, v___x_865_);
v_i_859_ = v___x_866_;
v_b_861_ = v___x_864_;
goto _start;
}
else
{
lean_dec(v___x_857_);
lean_dec(v_f_856_);
return v_b_861_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg___boxed(lean_object* v_f_868_, lean_object* v___x_869_, lean_object* v_as_870_, lean_object* v_i_871_, lean_object* v_stop_872_, lean_object* v_b_873_){
_start:
{
size_t v_i_boxed_874_; size_t v_stop_boxed_875_; lean_object* v_res_876_; 
v_i_boxed_874_ = lean_unbox_usize(v_i_871_);
lean_dec(v_i_871_);
v_stop_boxed_875_ = lean_unbox_usize(v_stop_872_);
lean_dec(v_stop_872_);
v_res_876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_868_, v___x_869_, v_as_870_, v_i_boxed_874_, v_stop_boxed_875_, v_b_873_);
lean_dec_ref(v_as_870_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_877_, lean_object* v___x_878_, lean_object* v_as_879_, lean_object* v_i_880_, lean_object* v_stop_881_, lean_object* v_b_882_){
_start:
{
size_t v_i_boxed_883_; size_t v_stop_boxed_884_; lean_object* v_res_885_; 
v_i_boxed_883_ = lean_unbox_usize(v_i_880_);
lean_dec(v_i_880_);
v_stop_boxed_884_ = lean_unbox_usize(v_stop_881_);
lean_dec(v_stop_881_);
v_res_885_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_877_, v___x_878_, v_as_879_, v_i_boxed_883_, v_stop_boxed_884_, v_b_882_);
lean_dec_ref(v_as_879_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg___boxed(lean_object* v_f_886_, lean_object* v___x_887_, lean_object* v_x_888_, lean_object* v_x_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(v_f_886_, v___x_887_, v_x_888_, v_x_889_);
lean_dec_ref(v_x_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg___boxed(lean_object* v_f_891_, lean_object* v___x_892_, lean_object* v_x_893_, lean_object* v_x_894_, lean_object* v_x_895_, lean_object* v_x_896_){
_start:
{
size_t v_x_1173__boxed_897_; size_t v_x_1174__boxed_898_; lean_object* v_res_899_; 
v_x_1173__boxed_897_ = lean_unbox_usize(v_x_894_);
lean_dec(v_x_894_);
v_x_1174__boxed_898_ = lean_unbox_usize(v_x_895_);
lean_dec(v_x_895_);
v_res_899_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(v_f_891_, v___x_892_, v_x_893_, v_x_1173__boxed_897_, v_x_1174__boxed_898_, v_x_896_);
lean_dec_ref(v_x_893_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg___boxed(lean_object* v_f_900_, lean_object* v___x_901_, lean_object* v_t_902_, lean_object* v_init_903_, lean_object* v_start_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(v_f_900_, v___x_901_, v_t_902_, v_init_903_, v_start_904_);
lean_dec(v_start_904_);
lean_dec_ref(v_t_902_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go(lean_object* v_00_u03b1_906_, lean_object* v_f_907_, lean_object* v_ctx_x3f_908_, lean_object* v_a_909_, lean_object* v_x_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(v_f_907_, v_ctx_x3f_908_, v_a_909_, v_x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0(lean_object* v_00_u03b1_912_, lean_object* v_f_913_, lean_object* v___x_914_, lean_object* v_t_915_, lean_object* v_init_916_, lean_object* v_start_917_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(v_f_913_, v___x_914_, v_t_915_, v_init_916_, v_start_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___boxed(lean_object* v_00_u03b1_919_, lean_object* v_f_920_, lean_object* v___x_921_, lean_object* v_t_922_, lean_object* v_init_923_, lean_object* v_start_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0(v_00_u03b1_919_, v_f_920_, v___x_921_, v_t_922_, v_init_923_, v_start_924_);
lean_dec(v_start_924_);
lean_dec_ref(v_t_922_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0(lean_object* v_00_u03b1_926_, lean_object* v_f_927_, lean_object* v___x_928_, lean_object* v_x_929_, size_t v_x_930_, size_t v_x_931_, lean_object* v_x_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(v_f_927_, v___x_928_, v_x_929_, v_x_930_, v_x_931_, v_x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_934_, lean_object* v_f_935_, lean_object* v___x_936_, lean_object* v_x_937_, lean_object* v_x_938_, lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
size_t v_x_1344__boxed_941_; size_t v_x_1345__boxed_942_; lean_object* v_res_943_; 
v_x_1344__boxed_941_ = lean_unbox_usize(v_x_938_);
lean_dec(v_x_938_);
v_x_1345__boxed_942_ = lean_unbox_usize(v_x_939_);
lean_dec(v_x_939_);
v_res_943_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0(v_00_u03b1_934_, v_f_935_, v___x_936_, v_x_937_, v_x_1344__boxed_941_, v_x_1345__boxed_942_, v_x_940_);
lean_dec_ref(v_x_937_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1(lean_object* v_00_u03b1_944_, lean_object* v_f_945_, lean_object* v___x_946_, lean_object* v_as_947_, size_t v_i_948_, size_t v_stop_949_, lean_object* v_b_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_945_, v___x_946_, v_as_947_, v_i_948_, v_stop_949_, v_b_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___boxed(lean_object* v_00_u03b1_952_, lean_object* v_f_953_, lean_object* v___x_954_, lean_object* v_as_955_, lean_object* v_i_956_, lean_object* v_stop_957_, lean_object* v_b_958_){
_start:
{
size_t v_i_boxed_959_; size_t v_stop_boxed_960_; lean_object* v_res_961_; 
v_i_boxed_959_ = lean_unbox_usize(v_i_956_);
lean_dec(v_i_956_);
v_stop_boxed_960_ = lean_unbox_usize(v_stop_957_);
lean_dec(v_stop_957_);
v_res_961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1(v_00_u03b1_952_, v_f_953_, v___x_954_, v_as_955_, v_i_boxed_959_, v_stop_boxed_960_, v_b_958_);
lean_dec_ref(v_as_955_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2(lean_object* v_00_u03b1_962_, lean_object* v_f_963_, lean_object* v___x_964_, lean_object* v_x_965_, lean_object* v_x_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(v_f_963_, v___x_964_, v_x_965_, v_x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___boxed(lean_object* v_00_u03b1_968_, lean_object* v_f_969_, lean_object* v___x_970_, lean_object* v_x_971_, lean_object* v_x_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2(v_00_u03b1_968_, v_f_969_, v___x_970_, v_x_971_, v_x_972_);
lean_dec_ref(v_x_971_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_974_, lean_object* v_f_975_, lean_object* v___x_976_, lean_object* v_as_977_, size_t v_i_978_, size_t v_stop_979_, lean_object* v_b_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_975_, v___x_976_, v_as_977_, v_i_978_, v_stop_979_, v_b_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_982_, lean_object* v_f_983_, lean_object* v___x_984_, lean_object* v_as_985_, lean_object* v_i_986_, lean_object* v_stop_987_, lean_object* v_b_988_){
_start:
{
size_t v_i_boxed_989_; size_t v_stop_boxed_990_; lean_object* v_res_991_; 
v_i_boxed_989_ = lean_unbox_usize(v_i_986_);
lean_dec(v_i_986_);
v_stop_boxed_990_ = lean_unbox_usize(v_stop_987_);
lean_dec(v_stop_987_);
v_res_991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1(v_00_u03b1_982_, v_f_983_, v___x_984_, v_as_985_, v_i_boxed_989_, v_stop_boxed_990_, v_b_988_);
lean_dec_ref(v_as_985_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoTree___redArg(lean_object* v_init_992_, lean_object* v_f_993_, lean_object* v_x_994_){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = lean_box(0);
v___x_996_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(v_f_993_, v___x_995_, v_init_992_, v_x_994_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoTree(lean_object* v_00_u03b1_997_, lean_object* v_init_998_, lean_object* v_f_999_, lean_object* v_x_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_Elab_InfoTree_foldInfoTree___redArg(v_init_998_, v_f_999_, v_x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0(lean_object* v_toPure_1002_, lean_object* v_result_1003_, lean_object* v_____do__lift_1004_){
_start:
{
if (lean_obj_tag(v_____do__lift_1004_) == 0)
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_apply_2(v_toPure_1002_, lean_box(0), v_result_1003_);
return v___x_1005_;
}
else
{
lean_object* v_val_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_val_1006_ = lean_ctor_get(v_____do__lift_1004_, 0);
lean_inc(v_val_1006_);
v___x_1007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1007_, 0, v_val_1006_);
lean_ctor_set(v___x_1007_, 1, v_result_1003_);
v___x_1008_ = lean_apply_2(v_toPure_1002_, lean_box(0), v___x_1007_);
return v___x_1008_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0___boxed(lean_object* v_toPure_1009_, lean_object* v_result_1010_, lean_object* v_____do__lift_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0(v_toPure_1009_, v_result_1010_, v_____do__lift_1011_);
lean_dec(v_____do__lift_1011_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__1(lean_object* v_toPure_1013_, lean_object* v_f_1014_, lean_object* v_toBind_1015_, lean_object* v_ctx_1016_, lean_object* v_info_1017_, lean_object* v_result_1018_){
_start:
{
if (lean_obj_tag(v_info_1017_) == 1)
{
lean_object* v_i_1019_; lean_object* v___f_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_i_1019_ = lean_ctor_get(v_info_1017_, 0);
lean_inc_ref(v_i_1019_);
lean_dec_ref_known(v_info_1017_, 1);
v___f_1020_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1020_, 0, v_toPure_1013_);
lean_closure_set(v___f_1020_, 1, v_result_1018_);
v___x_1021_ = lean_apply_2(v_f_1014_, v_ctx_1016_, v_i_1019_);
v___x_1022_ = lean_apply_4(v_toBind_1015_, lean_box(0), lean_box(0), v___x_1021_, v___f_1020_);
return v___x_1022_;
}
else
{
lean_object* v___x_1023_; 
lean_dec_ref(v_info_1017_);
lean_dec_ref(v_ctx_1016_);
lean_dec(v_toBind_1015_);
lean_dec(v_f_1014_);
v___x_1023_ = lean_apply_2(v_toPure_1013_, lean_box(0), v_result_1018_);
return v___x_1023_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___redArg(lean_object* v_inst_1024_, lean_object* v_t_1025_, lean_object* v_f_1026_){
_start:
{
lean_object* v_toApplicative_1027_; lean_object* v_toBind_1028_; lean_object* v_toPure_1029_; lean_object* v___f_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v_toApplicative_1027_ = lean_ctor_get(v_inst_1024_, 0);
v_toBind_1028_ = lean_ctor_get(v_inst_1024_, 1);
v_toPure_1029_ = lean_ctor_get(v_toApplicative_1027_, 1);
lean_inc(v_toBind_1028_);
lean_inc(v_toPure_1029_);
v___f_1030_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__1), 6, 3);
lean_closure_set(v___f_1030_, 0, v_toPure_1029_);
lean_closure_set(v___f_1030_, 1, v_f_1026_);
lean_closure_set(v___f_1030_, 2, v_toBind_1028_);
v___x_1031_ = lean_box(0);
v___x_1032_ = l_Lean_Elab_InfoTree_foldInfoM___redArg(v_inst_1024_, v___f_1030_, v___x_1031_, v_t_1025_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM(lean_object* v_m_1033_, lean_object* v_00_u03b1_1034_, lean_object* v_inst_1035_, lean_object* v_t_1036_, lean_object* v_f_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_Elab_InfoTree_collectTermInfoM___redArg(v_inst_1035_, v_t_1036_, v_f_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Info_isTerm(lean_object* v_x_1039_){
_start:
{
if (lean_obj_tag(v_x_1039_) == 1)
{
uint8_t v___x_1040_; 
v___x_1040_ = 1;
return v___x_1040_;
}
else
{
uint8_t v___x_1041_; 
v___x_1041_ = 0;
return v___x_1041_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_isTerm___boxed(lean_object* v_x_1042_){
_start:
{
uint8_t v_res_1043_; lean_object* v_r_1044_; 
v_res_1043_ = l_Lean_Elab_Info_isTerm(v_x_1042_);
lean_dec_ref(v_x_1042_);
v_r_1044_ = lean_box(v_res_1043_);
return v_r_1044_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Info_isCompletion(lean_object* v_x_1045_){
_start:
{
if (lean_obj_tag(v_x_1045_) == 8)
{
uint8_t v___x_1046_; 
v___x_1046_ = 1;
return v___x_1046_;
}
else
{
uint8_t v___x_1047_; 
v___x_1047_ = 0;
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_isCompletion___boxed(lean_object* v_x_1048_){
_start:
{
uint8_t v_res_1049_; lean_object* v_r_1050_; 
v_res_1049_ = l_Lean_Elab_Info_isCompletion(v_x_1048_);
lean_dec_ref(v_x_1048_);
v_r_1050_ = lean_box(v_res_1049_);
return v_r_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_getCompletionInfos___lam__0(lean_object* v_ctx_1051_, lean_object* v_info_1052_, lean_object* v_result_1053_){
_start:
{
if (lean_obj_tag(v_info_1052_) == 8)
{
lean_object* v_i_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_i_1054_ = lean_ctor_get(v_info_1052_, 0);
lean_inc_ref(v_i_1054_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v_ctx_1051_);
lean_ctor_set(v___x_1055_, 1, v_i_1054_);
v___x_1056_ = lean_array_push(v_result_1053_, v___x_1055_);
return v___x_1056_;
}
else
{
lean_dec_ref(v_ctx_1051_);
return v_result_1053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_getCompletionInfos___lam__0___boxed(lean_object* v_ctx_1057_, lean_object* v_info_1058_, lean_object* v_result_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Elab_InfoTree_getCompletionInfos___lam__0(v_ctx_1057_, v_info_1058_, v_result_1059_);
lean_dec_ref(v_info_1058_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_getCompletionInfos(lean_object* v_infoTree_1064_){
_start:
{
lean_object* v___f_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___f_1065_ = ((lean_object*)(l_Lean_Elab_InfoTree_getCompletionInfos___closed__0));
v___x_1066_ = ((lean_object*)(l_Lean_Elab_InfoTree_getCompletionInfos___closed__1));
v___x_1067_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_1065_, v___x_1066_, v_infoTree_1064_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_lctx(lean_object* v_x_1068_){
_start:
{
switch(lean_obj_tag(v_x_1068_))
{
case 1:
{
lean_object* v_i_1069_; lean_object* v_lctx_1070_; 
v_i_1069_ = lean_ctor_get(v_x_1068_, 0);
v_lctx_1070_ = lean_ctor_get(v_i_1069_, 1);
lean_inc_ref(v_lctx_1070_);
return v_lctx_1070_;
}
case 7:
{
lean_object* v_i_1071_; lean_object* v_lctx_1072_; 
v_i_1071_ = lean_ctor_get(v_x_1068_, 0);
v_lctx_1072_ = lean_ctor_get(v_i_1071_, 2);
lean_inc_ref(v_lctx_1072_);
return v_lctx_1072_;
}
case 13:
{
lean_object* v_i_1073_; lean_object* v_toTermInfo_1074_; lean_object* v_lctx_1075_; 
v_i_1073_ = lean_ctor_get(v_x_1068_, 0);
v_toTermInfo_1074_ = lean_ctor_get(v_i_1073_, 0);
v_lctx_1075_ = lean_ctor_get(v_toTermInfo_1074_, 1);
lean_inc_ref(v_lctx_1075_);
return v_lctx_1075_;
}
case 4:
{
lean_object* v_i_1076_; lean_object* v_lctx_1077_; 
v_i_1076_ = lean_ctor_get(v_x_1068_, 0);
v_lctx_1077_ = lean_ctor_get(v_i_1076_, 0);
lean_inc_ref(v_lctx_1077_);
return v_lctx_1077_;
}
case 8:
{
lean_object* v_i_1078_; lean_object* v___x_1079_; 
v_i_1078_ = lean_ctor_get(v_x_1068_, 0);
v___x_1079_ = l_Lean_Elab_CompletionInfo_lctx(v_i_1078_);
return v___x_1079_;
}
default: 
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_LocalContext_empty;
return v___x_1080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_lctx___boxed(lean_object* v_x_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_Elab_Info_lctx(v_x_1081_);
lean_dec_ref(v_x_1081_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_pos_x3f(lean_object* v_i_1083_){
_start:
{
lean_object* v___x_1084_; uint8_t v___x_1085_; lean_object* v___x_1086_; 
v___x_1084_ = l_Lean_Elab_Info_stx(v_i_1083_);
v___x_1085_ = 1;
v___x_1086_ = l_Lean_Syntax_getPos_x3f(v___x_1084_, v___x_1085_);
lean_dec(v___x_1084_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_pos_x3f___boxed(lean_object* v_i_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_Elab_Info_pos_x3f(v_i_1087_);
lean_dec_ref(v_i_1087_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_tailPos_x3f(lean_object* v_i_1089_){
_start:
{
lean_object* v___x_1090_; uint8_t v___x_1091_; lean_object* v___x_1092_; 
v___x_1090_ = l_Lean_Elab_Info_stx(v_i_1089_);
v___x_1091_ = 1;
v___x_1092_ = l_Lean_Syntax_getTailPos_x3f(v___x_1090_, v___x_1091_);
lean_dec(v___x_1090_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_tailPos_x3f___boxed(lean_object* v_i_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_Elab_Info_tailPos_x3f(v_i_1093_);
lean_dec_ref(v_i_1093_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_range_x3f(lean_object* v_i_1095_){
_start:
{
lean_object* v___x_1096_; uint8_t v___x_1097_; lean_object* v___x_1098_; 
v___x_1096_ = l_Lean_Elab_Info_stx(v_i_1095_);
v___x_1097_ = 1;
v___x_1098_ = l_Lean_Syntax_getRange_x3f(v___x_1096_, v___x_1097_);
lean_dec(v___x_1096_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_range_x3f___boxed(lean_object* v_i_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lean_Elab_Info_range_x3f(v_i_1099_);
lean_dec_ref(v_i_1099_);
return v_res_1100_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Info_contains(lean_object* v_i_1101_, lean_object* v_pos_1102_, uint8_t v_includeStop_1103_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Lean_Elab_Info_range_x3f(v_i_1101_);
if (lean_obj_tag(v___x_1104_) == 0)
{
uint8_t v___x_1105_; 
v___x_1105_ = 0;
return v___x_1105_;
}
else
{
lean_object* v_val_1106_; uint8_t v___x_1107_; 
v_val_1106_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_val_1106_);
lean_dec_ref_known(v___x_1104_, 1);
v___x_1107_ = l_Lean_Syntax_Range_contains(v_val_1106_, v_pos_1102_, v_includeStop_1103_);
lean_dec(v_val_1106_);
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_contains___boxed(lean_object* v_i_1108_, lean_object* v_pos_1109_, lean_object* v_includeStop_1110_){
_start:
{
uint8_t v_includeStop_boxed_1111_; uint8_t v_res_1112_; lean_object* v_r_1113_; 
v_includeStop_boxed_1111_ = lean_unbox(v_includeStop_1110_);
v_res_1112_ = l_Lean_Elab_Info_contains(v_i_1108_, v_pos_1109_, v_includeStop_boxed_1111_);
lean_dec(v_pos_1109_);
lean_dec_ref(v_i_1108_);
v_r_1113_ = lean_box(v_res_1112_);
return v_r_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_size_x3f(lean_object* v_i_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_Elab_Info_pos_x3f(v_i_1114_);
if (lean_obj_tag(v___x_1115_) == 0)
{
return v___x_1115_;
}
else
{
lean_object* v_val_1116_; lean_object* v___x_1117_; 
v_val_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_val_1116_);
lean_dec_ref_known(v___x_1115_, 1);
v___x_1117_ = l_Lean_Elab_Info_tailPos_x3f(v_i_1114_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_dec(v_val_1116_);
return v___x_1117_;
}
else
{
lean_object* v_val_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1126_; 
v_val_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1126_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_val_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1126_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v___x_1124_; 
v___x_1122_ = lean_nat_sub(v_val_1118_, v_val_1116_);
lean_dec(v_val_1116_);
lean_dec(v_val_1118_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1122_);
v___x_1124_ = v___x_1120_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_size_x3f___boxed(lean_object* v_i_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_Elab_Info_size_x3f(v_i_1127_);
lean_dec_ref(v_i_1127_);
return v_res_1128_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Info_isSmaller(lean_object* v_i_u2081_1129_, lean_object* v_i_u2082_1130_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_Elab_Info_size_x3f(v_i_u2081_1129_);
if (lean_obj_tag(v___x_1131_) == 1)
{
lean_object* v_val_1132_; lean_object* v___x_1133_; 
v_val_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_val_1132_);
lean_dec_ref_known(v___x_1131_, 1);
v___x_1133_ = l_Lean_Elab_Info_size_x3f(v_i_u2082_1130_);
if (lean_obj_tag(v___x_1133_) == 0)
{
uint8_t v___x_1134_; 
lean_dec(v_val_1132_);
v___x_1134_ = 1;
return v___x_1134_;
}
else
{
lean_object* v_val_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
v_val_1135_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_val_1135_);
lean_dec_ref_known(v___x_1133_, 1);
v___x_1136_ = lean_unsigned_to_nat(1u);
v___x_1137_ = lean_nat_add(v_val_1132_, v___x_1136_);
lean_dec(v_val_1132_);
v___x_1138_ = lean_nat_dec_le(v___x_1137_, v_val_1135_);
lean_dec(v_val_1135_);
lean_dec(v___x_1137_);
return v___x_1138_;
}
}
else
{
uint8_t v___x_1139_; 
lean_dec(v___x_1131_);
v___x_1139_ = 0;
return v___x_1139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_isSmaller___boxed(lean_object* v_i_u2081_1140_, lean_object* v_i_u2082_1141_){
_start:
{
uint8_t v_res_1142_; lean_object* v_r_1143_; 
v_res_1142_ = l_Lean_Elab_Info_isSmaller(v_i_u2081_1140_, v_i_u2082_1141_);
lean_dec_ref(v_i_u2082_1141_);
lean_dec_ref(v_i_u2081_1140_);
v_r_1143_ = lean_box(v_res_1142_);
return v_r_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_occursInside_x3f(lean_object* v_i_1144_, lean_object* v_hoverPos_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_Elab_Info_pos_x3f(v_i_1144_);
if (lean_obj_tag(v___x_1146_) == 0)
{
return v___x_1146_;
}
else
{
lean_object* v_val_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1164_; 
v_val_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1164_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_val_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1164_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
uint8_t v___y_1152_; lean_object* v___x_1158_; 
v___x_1158_ = l_Lean_Elab_Info_tailPos_x3f(v_i_1144_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_del_object(v___x_1149_);
lean_dec(v_val_1147_);
return v___x_1158_;
}
else
{
lean_object* v_val_1159_; uint8_t v___x_1160_; 
v_val_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_val_1159_);
lean_dec_ref_known(v___x_1158_, 1);
v___x_1160_ = lean_nat_dec_le(v_val_1147_, v_hoverPos_1145_);
if (v___x_1160_ == 0)
{
lean_dec(v_val_1159_);
v___y_1152_ = v___x_1160_;
goto v___jp_1151_;
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1161_ = lean_unsigned_to_nat(1u);
v___x_1162_ = lean_nat_add(v_hoverPos_1145_, v___x_1161_);
v___x_1163_ = lean_nat_dec_le(v___x_1162_, v_val_1159_);
lean_dec(v_val_1159_);
lean_dec(v___x_1162_);
v___y_1152_ = v___x_1163_;
goto v___jp_1151_;
}
}
v___jp_1151_:
{
if (v___y_1152_ == 0)
{
lean_object* v___x_1153_; 
lean_del_object(v___x_1149_);
lean_dec(v_val_1147_);
v___x_1153_ = lean_box(0);
return v___x_1153_;
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1154_ = lean_nat_sub(v_hoverPos_1145_, v_val_1147_);
lean_dec(v_val_1147_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1154_);
v___x_1156_ = v___x_1149_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Info_occursInside_x3f___boxed(lean_object* v_i_1165_, lean_object* v_hoverPos_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_Elab_Info_occursInside_x3f(v_i_1165_, v_hoverPos_1166_);
lean_dec(v_hoverPos_1166_);
lean_dec_ref(v_i_1165_);
return v_res_1167_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Info_occursInOrOnBoundary(lean_object* v_i_1168_, lean_object* v_hoverPos_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_Elab_Info_pos_x3f(v_i_1168_);
if (lean_obj_tag(v___x_1170_) == 1)
{
lean_object* v_val_1171_; lean_object* v___x_1172_; 
v_val_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_val_1171_);
lean_dec_ref_known(v___x_1170_, 1);
v___x_1172_ = l_Lean_Elab_Info_tailPos_x3f(v_i_1168_);
if (lean_obj_tag(v___x_1172_) == 1)
{
lean_object* v_val_1173_; uint8_t v___x_1174_; 
v_val_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_val_1173_);
lean_dec_ref_known(v___x_1172_, 1);
v___x_1174_ = lean_nat_dec_le(v_val_1171_, v_hoverPos_1169_);
lean_dec(v_val_1171_);
if (v___x_1174_ == 0)
{
lean_dec(v_val_1173_);
return v___x_1174_;
}
else
{
uint8_t v___x_1175_; 
v___x_1175_ = lean_nat_dec_le(v_hoverPos_1169_, v_val_1173_);
lean_dec(v_val_1173_);
return v___x_1175_;
}
}
else
{
uint8_t v___x_1176_; 
lean_dec(v___x_1172_);
lean_dec(v_val_1171_);
v___x_1176_ = 0;
return v___x_1176_;
}
}
else
{
uint8_t v___x_1177_; 
lean_dec(v___x_1170_);
v___x_1177_ = 0;
return v___x_1177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_occursInOrOnBoundary___boxed(lean_object* v_i_1178_, lean_object* v_hoverPos_1179_){
_start:
{
uint8_t v_res_1180_; lean_object* v_r_1181_; 
v_res_1180_ = l_Lean_Elab_Info_occursInOrOnBoundary(v_i_1178_, v_hoverPos_1179_);
lean_dec(v_hoverPos_1179_);
lean_dec_ref(v_i_1178_);
v_r_1181_ = lean_box(v_res_1180_);
return v_r_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0(lean_object* v_p_1182_, lean_object* v_ctx_1183_, lean_object* v_i_1184_, lean_object* v_x_1185_){
_start:
{
lean_object* v___x_1186_; uint8_t v___x_1187_; 
lean_inc_ref(v_i_1184_);
v___x_1186_ = lean_apply_1(v_p_1182_, v_i_1184_);
v___x_1187_ = lean_unbox(v___x_1186_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; 
lean_dec_ref(v_i_1184_);
lean_dec_ref(v_ctx_1183_);
v___x_1188_ = lean_box(0);
return v___x_1188_;
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v_ctx_1183_);
lean_ctor_set(v___x_1189_, 1, v_i_1184_);
v___x_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0___boxed(lean_object* v_p_1191_, lean_object* v_ctx_1192_, lean_object* v_i_1193_, lean_object* v_x_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0(v_p_1191_, v_ctx_1192_, v_i_1193_, v_x_1194_);
lean_dec_ref(v_x_1194_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(lean_object* v_as_1196_, size_t v_i_1197_, size_t v_stop_1198_, lean_object* v_b_1199_){
_start:
{
lean_object* v___y_1201_; uint8_t v___x_1205_; 
v___x_1205_ = lean_usize_dec_eq(v_i_1197_, v_stop_1198_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; lean_object* v_fst_1207_; lean_object* v_fst_1208_; uint8_t v___x_1209_; 
v___x_1206_ = lean_array_uget_borrowed(v_as_1196_, v_i_1197_);
v_fst_1207_ = lean_ctor_get(v___x_1206_, 0);
v_fst_1208_ = lean_ctor_get(v_b_1199_, 0);
v___x_1209_ = lean_nat_dec_lt(v_fst_1207_, v_fst_1208_);
if (v___x_1209_ == 0)
{
v___y_1201_ = v_b_1199_;
goto v___jp_1200_;
}
else
{
v___y_1201_ = v___x_1206_;
goto v___jp_1200_;
}
}
else
{
lean_inc_ref(v_b_1199_);
return v_b_1199_;
}
v___jp_1200_:
{
size_t v___x_1202_; size_t v___x_1203_; 
v___x_1202_ = ((size_t)1ULL);
v___x_1203_ = lean_usize_add(v_i_1197_, v___x_1202_);
v_i_1197_ = v___x_1203_;
v_b_1199_ = v___y_1201_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1___boxed(lean_object* v_as_1210_, lean_object* v_i_1211_, lean_object* v_stop_1212_, lean_object* v_b_1213_){
_start:
{
size_t v_i_boxed_1214_; size_t v_stop_boxed_1215_; lean_object* v_res_1216_; 
v_i_boxed_1214_ = lean_unbox_usize(v_i_1211_);
lean_dec(v_i_1211_);
v_stop_boxed_1215_ = lean_unbox_usize(v_stop_1212_);
lean_dec(v_stop_1212_);
v_res_1216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(v_as_1210_, v_i_boxed_1214_, v_stop_boxed_1215_, v_b_1213_);
lean_dec_ref(v_b_1213_);
lean_dec_ref(v_as_1210_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1(lean_object* v_as_1217_){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1218_ = lean_unsigned_to_nat(0u);
v___x_1219_ = lean_array_get_size(v_as_1217_);
v___x_1220_ = lean_nat_dec_lt(v___x_1218_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_box(0);
return v___x_1221_;
}
else
{
lean_object* v_a0_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v_a0_1222_ = lean_array_fget_borrowed(v_as_1217_, v___x_1218_);
v___x_1223_ = lean_unsigned_to_nat(1u);
v___x_1224_ = lean_nat_dec_lt(v___x_1223_, v___x_1219_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; 
lean_inc(v_a0_1222_);
v___x_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1225_, 0, v_a0_1222_);
return v___x_1225_;
}
else
{
size_t v___x_1226_; size_t v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1226_ = ((size_t)1ULL);
v___x_1227_ = lean_usize_of_nat(v___x_1219_);
v___x_1228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(v_as_1217_, v___x_1226_, v___x_1227_, v_a0_1222_);
v___x_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
return v___x_1229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1___boxed(lean_object* v_as_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1(v_as_1230_);
lean_dec_ref(v_as_1230_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__0(lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
if (lean_obj_tag(v_a_1232_) == 0)
{
lean_object* v___x_1234_; 
v___x_1234_ = lean_array_to_list(v_a_1233_);
return v___x_1234_;
}
else
{
lean_object* v_head_1235_; lean_object* v_tail_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1253_; 
v_head_1235_ = lean_ctor_get(v_a_1232_, 0);
v_tail_1236_ = lean_ctor_get(v_a_1232_, 1);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_a_1232_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1238_ = v_a_1232_;
v_isShared_1239_ = v_isSharedCheck_1253_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_tail_1236_);
lean_inc(v_head_1235_);
lean_dec(v_a_1232_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1253_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v_snd_1240_; lean_object* v___x_1241_; 
v_snd_1240_ = lean_ctor_get(v_head_1235_, 1);
v___x_1241_ = l_Lean_Elab_Info_pos_x3f(v_snd_1240_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_del_object(v___x_1238_);
lean_dec(v_head_1235_);
v_a_1232_ = v_tail_1236_;
goto _start;
}
else
{
lean_object* v_val_1243_; lean_object* v___x_1244_; 
v_val_1243_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_val_1243_);
lean_dec_ref_known(v___x_1241_, 1);
v___x_1244_ = l_Lean_Elab_Info_tailPos_x3f(v_snd_1240_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_dec(v_val_1243_);
lean_del_object(v___x_1238_);
lean_dec(v_head_1235_);
v_a_1232_ = v_tail_1236_;
goto _start;
}
else
{
lean_object* v_val_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
v_val_1246_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_val_1246_);
lean_dec_ref_known(v___x_1244_, 1);
v___x_1247_ = lean_nat_sub(v_val_1246_, v_val_1243_);
lean_dec(v_val_1243_);
lean_dec(v_val_1246_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set_tag(v___x_1238_, 0);
lean_ctor_set(v___x_1238_, 1, v_head_1235_);
lean_ctor_set(v___x_1238_, 0, v___x_1247_);
v___x_1249_ = v___x_1238_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_head_1235_);
v___x_1249_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1250_; 
v___x_1250_ = lean_array_push(v_a_1233_, v___x_1249_);
v_a_1232_ = v_tail_1236_;
v_a_1233_ = v___x_1250_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f(lean_object* v_p_1256_, lean_object* v_t_1257_){
_start:
{
lean_object* v___f_1258_; lean_object* v_ts_1259_; lean_object* v___x_1260_; lean_object* v_infos_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___f_1258_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1258_, 0, v_p_1256_);
v_ts_1259_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_1258_, v_t_1257_);
v___x_1260_ = ((lean_object*)(l_Lean_Elab_InfoTree_smallestInfo_x3f___closed__0));
v_infos_1261_ = l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__0(v_ts_1259_, v___x_1260_);
v___x_1262_ = lean_array_mk(v_infos_1261_);
v___x_1263_ = l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1(v___x_1262_);
lean_dec_ref(v___x_1262_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_box(0);
return v___x_1264_;
}
else
{
lean_object* v_val_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1273_; 
v_val_1265_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1267_ = v___x_1263_;
v_isShared_1268_ = v_isSharedCheck_1273_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_val_1265_);
lean_dec(v___x_1263_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1273_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v_snd_1269_; lean_object* v___x_1271_; 
v_snd_1269_ = lean_ctor_get(v_val_1265_, 1);
lean_inc(v_snd_1269_);
lean_dec(v_val_1265_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v_snd_1269_);
v___x_1271_ = v___x_1267_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_snd_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_instBEqHoverableInfoPrio_beq(lean_object* v_x_1274_, lean_object* v_x_1275_){
_start:
{
uint8_t v_isHoverPosOnStop_1276_; lean_object* v_size_1277_; uint8_t v_isVariableInfo_1278_; uint8_t v_isPartialTermInfo_1279_; uint8_t v_isHoverPosOnStop_1280_; lean_object* v_size_1281_; uint8_t v_isVariableInfo_1282_; uint8_t v_isPartialTermInfo_1283_; uint8_t v___y_1285_; 
v_isHoverPosOnStop_1276_ = lean_ctor_get_uint8(v_x_1274_, sizeof(void*)*1);
v_size_1277_ = lean_ctor_get(v_x_1274_, 0);
v_isVariableInfo_1278_ = lean_ctor_get_uint8(v_x_1274_, sizeof(void*)*1 + 1);
v_isPartialTermInfo_1279_ = lean_ctor_get_uint8(v_x_1274_, sizeof(void*)*1 + 2);
v_isHoverPosOnStop_1280_ = lean_ctor_get_uint8(v_x_1275_, sizeof(void*)*1);
v_size_1281_ = lean_ctor_get(v_x_1275_, 0);
v_isVariableInfo_1282_ = lean_ctor_get_uint8(v_x_1275_, sizeof(void*)*1 + 1);
v_isPartialTermInfo_1283_ = lean_ctor_get_uint8(v_x_1275_, sizeof(void*)*1 + 2);
if (v_isHoverPosOnStop_1280_ == 0)
{
if (v_isHoverPosOnStop_1276_ == 0)
{
goto v___jp_1286_;
}
else
{
return v_isHoverPosOnStop_1280_;
}
}
else
{
if (v_isHoverPosOnStop_1276_ == 0)
{
return v_isHoverPosOnStop_1276_;
}
else
{
goto v___jp_1286_;
}
}
v___jp_1284_:
{
if (v___y_1285_ == 0)
{
return v___y_1285_;
}
else
{
if (v_isPartialTermInfo_1283_ == 0)
{
if (v_isPartialTermInfo_1279_ == 0)
{
return v___y_1285_;
}
else
{
return v_isPartialTermInfo_1283_;
}
}
else
{
return v_isPartialTermInfo_1279_;
}
}
}
v___jp_1286_:
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_nat_dec_eq(v_size_1277_, v_size_1281_);
if (v___x_1287_ == 0)
{
return v___x_1287_;
}
else
{
if (v_isVariableInfo_1282_ == 0)
{
if (v_isVariableInfo_1278_ == 0)
{
v___y_1285_ = v___x_1287_;
goto v___jp_1284_;
}
else
{
return v_isVariableInfo_1282_;
}
}
else
{
v___y_1285_ = v_isVariableInfo_1278_;
goto v___jp_1284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instBEqHoverableInfoPrio_beq___boxed(lean_object* v_x_1288_, lean_object* v_x_1289_){
_start:
{
uint8_t v_res_1290_; lean_object* v_r_1291_; 
v_res_1290_ = l_Lean_Elab_instBEqHoverableInfoPrio_beq(v_x_1288_, v_x_1289_);
lean_dec_ref(v_x_1289_);
lean_dec_ref(v_x_1288_);
v_r_1291_ = lean_box(v_res_1290_);
return v_r_1291_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(lean_object* v_i1_1294_, lean_object* v_i2_1295_){
_start:
{
uint8_t v_isHoverPosOnStop_1296_; lean_object* v_size_1297_; uint8_t v_isVariableInfo_1298_; uint8_t v_isPartialTermInfo_1299_; uint8_t v___y_1301_; uint8_t v___y_1324_; 
v_isHoverPosOnStop_1296_ = lean_ctor_get_uint8(v_i1_1294_, sizeof(void*)*1);
v_size_1297_ = lean_ctor_get(v_i1_1294_, 0);
v_isVariableInfo_1298_ = lean_ctor_get_uint8(v_i1_1294_, sizeof(void*)*1 + 1);
v_isPartialTermInfo_1299_ = lean_ctor_get_uint8(v_i1_1294_, sizeof(void*)*1 + 2);
if (v_isHoverPosOnStop_1296_ == 0)
{
v___y_1324_ = v_isHoverPosOnStop_1296_;
goto v___jp_1323_;
}
else
{
uint8_t v_isHoverPosOnStop_1325_; 
v_isHoverPosOnStop_1325_ = lean_ctor_get_uint8(v_i2_1295_, sizeof(void*)*1);
if (v_isHoverPosOnStop_1325_ == 0)
{
uint8_t v___x_1326_; 
v___x_1326_ = 0;
return v___x_1326_;
}
else
{
uint8_t v___x_1327_; 
v___x_1327_ = 0;
v___y_1324_ = v___x_1327_;
goto v___jp_1323_;
}
}
v___jp_1300_:
{
if (v_isPartialTermInfo_1299_ == 0)
{
uint8_t v_isPartialTermInfo_1302_; 
v_isPartialTermInfo_1302_ = lean_ctor_get_uint8(v_i2_1295_, sizeof(void*)*1 + 2);
if (v_isPartialTermInfo_1302_ == 0)
{
uint8_t v___x_1303_; 
v___x_1303_ = 1;
return v___x_1303_;
}
else
{
uint8_t v___x_1304_; 
v___x_1304_ = 2;
return v___x_1304_;
}
}
else
{
uint8_t v_isPartialTermInfo_1305_; 
v_isPartialTermInfo_1305_ = lean_ctor_get_uint8(v_i2_1295_, sizeof(void*)*1 + 2);
if (v_isPartialTermInfo_1305_ == 0)
{
uint8_t v___x_1306_; 
v___x_1306_ = 0;
return v___x_1306_;
}
else
{
if (v___y_1301_ == 0)
{
uint8_t v___x_1307_; 
v___x_1307_ = 1;
return v___x_1307_;
}
else
{
uint8_t v___x_1308_; 
v___x_1308_ = 0;
return v___x_1308_;
}
}
}
}
v___jp_1309_:
{
uint8_t v_isVariableInfo_1310_; 
v_isVariableInfo_1310_ = lean_ctor_get_uint8(v_i2_1295_, sizeof(void*)*1 + 1);
if (v_isVariableInfo_1310_ == 0)
{
v___y_1301_ = v_isVariableInfo_1310_;
goto v___jp_1300_;
}
else
{
uint8_t v___x_1311_; 
v___x_1311_ = 2;
return v___x_1311_;
}
}
v___jp_1312_:
{
lean_object* v_size_1313_; uint8_t v_isVariableInfo_1314_; uint8_t v___x_1315_; 
v_size_1313_ = lean_ctor_get(v_i2_1295_, 0);
v_isVariableInfo_1314_ = lean_ctor_get_uint8(v_i2_1295_, sizeof(void*)*1 + 1);
v___x_1315_ = lean_nat_dec_lt(v_size_1313_, v_size_1297_);
if (v___x_1315_ == 0)
{
uint8_t v___x_1316_; 
v___x_1316_ = lean_nat_dec_lt(v_size_1297_, v_size_1313_);
if (v___x_1316_ == 0)
{
if (v_isVariableInfo_1298_ == 0)
{
goto v___jp_1309_;
}
else
{
if (v_isVariableInfo_1314_ == 0)
{
uint8_t v___x_1317_; 
v___x_1317_ = 0;
return v___x_1317_;
}
else
{
if (v___x_1316_ == 0)
{
v___y_1301_ = v___x_1316_;
goto v___jp_1300_;
}
else
{
goto v___jp_1309_;
}
}
}
}
else
{
uint8_t v___x_1318_; 
v___x_1318_ = 2;
return v___x_1318_;
}
}
else
{
uint8_t v___x_1319_; 
v___x_1319_ = 0;
return v___x_1319_;
}
}
v___jp_1320_:
{
uint8_t v_isHoverPosOnStop_1321_; 
v_isHoverPosOnStop_1321_ = lean_ctor_get_uint8(v_i2_1295_, sizeof(void*)*1);
if (v_isHoverPosOnStop_1321_ == 0)
{
goto v___jp_1312_;
}
else
{
uint8_t v___x_1322_; 
v___x_1322_ = 2;
return v___x_1322_;
}
}
v___jp_1323_:
{
if (v_isHoverPosOnStop_1296_ == 0)
{
goto v___jp_1320_;
}
else
{
if (v___y_1324_ == 0)
{
goto v___jp_1312_;
}
else
{
goto v___jp_1320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instOrdHoverableInfoPrio___lam__0___boxed(lean_object* v_i1_1328_, lean_object* v_i2_1329_){
_start:
{
uint8_t v_res_1330_; lean_object* v_r_1331_; 
v_res_1330_ = l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(v_i1_1328_, v_i2_1329_);
lean_dec_ref(v_i2_1329_);
lean_dec_ref(v_i1_1328_);
v_r_1331_ = lean_box(v_res_1330_);
return v_r_1331_;
}
}
static lean_object* _init_l_Lean_Elab_instLEHoverableInfoPrio(void){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_box(0);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMaxHoverableInfoPrio___lam__0(lean_object* v_x_1335_, lean_object* v_y_1336_){
_start:
{
uint8_t v___x_1337_; 
v___x_1337_ = l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(v_x_1335_, v_y_1336_);
if (v___x_1337_ == 2)
{
lean_inc_ref(v_x_1335_);
return v_x_1335_;
}
else
{
lean_inc_ref(v_y_1336_);
return v_y_1336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMaxHoverableInfoPrio___lam__0___boxed(lean_object* v_x_1338_, lean_object* v_y_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_Elab_instMaxHoverableInfoPrio___lam__0(v_x_1338_, v_y_1339_);
lean_dec_ref(v_y_1339_);
lean_dec_ref(v_x_1338_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0(lean_object* v_x_1343_){
_start:
{
lean_object* v_fst_1344_; 
v_fst_1344_ = lean_ctor_get(v_x_1343_, 0);
lean_inc(v_fst_1344_);
return v_fst_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0___boxed(lean_object* v_x_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0(v_x_1345_);
lean_dec_ref(v_x_1345_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1(lean_object* v_r_x3f_1347_){
_start:
{
if (lean_obj_tag(v_r_x3f_1347_) == 0)
{
lean_object* v___x_1348_; 
v___x_1348_ = lean_box(0);
return v___x_1348_;
}
else
{
lean_object* v_val_1349_; 
v_val_1349_ = lean_ctor_get(v_r_x3f_1347_, 0);
lean_inc(v_val_1349_);
return v_val_1349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1___boxed(lean_object* v_r_x3f_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1(v_r_x3f_1350_);
lean_dec(v_r_x3f_1350_);
return v_res_1351_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2(lean_object* v___x_1352_, lean_object* v_maxPrio_x3f_1353_, lean_object* v_x_1354_){
_start:
{
lean_object* v_fst_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v_fst_1355_ = lean_ctor_get(v_x_1354_, 0);
lean_inc(v_fst_1355_);
v___x_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_fst_1355_);
v___x_1357_ = l_Option_instBEq_beq___redArg(v___x_1352_, v___x_1356_, v_maxPrio_x3f_1353_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2___boxed(lean_object* v___x_1358_, lean_object* v_maxPrio_x3f_1359_, lean_object* v_x_1360_){
_start:
{
uint8_t v_res_1361_; lean_object* v_r_1362_; 
v_res_1361_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2(v___x_1358_, v_maxPrio_x3f_1359_, v_x_1360_);
lean_dec_ref(v_x_1360_);
v_r_1362_ = lean_box(v_res_1361_);
return v_r_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3(lean_object* v___f_1375_, lean_object* v___f_1376_, lean_object* v___x_1377_, lean_object* v_toPure_1378_, lean_object* v_ctx_1379_, lean_object* v_info_1380_, lean_object* v_children_1381_, lean_object* v_hoverPos_1382_, uint8_t v_includeStop_1383_, lean_object* v_results_1384_){
_start:
{
uint8_t v___y_1386_; uint8_t v___y_1387_; lean_object* v___y_1388_; uint8_t v___y_1389_; uint8_t v___y_1396_; uint8_t v___y_1397_; lean_object* v___y_1398_; uint8_t v___y_1399_; uint8_t v___y_1400_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v_maxPrio_x3f_1406_; lean_object* v___f_1407_; lean_object* v_bestResult_x3f_1408_; 
v___x_1404_ = lean_box(0);
lean_inc(v_results_1384_);
v___x_1405_ = l_List_mapTR_loop___redArg(v___f_1375_, v_results_1384_, v___x_1404_);
v_maxPrio_x3f_1406_ = l_List_max_x3f___redArg(v___f_1376_, v___x_1405_);
v___f_1407_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_1407_, 0, v___x_1377_);
lean_closure_set(v___f_1407_, 1, v_maxPrio_x3f_1406_);
v_bestResult_x3f_1408_ = l_List_find_x3f___redArg(v___f_1407_, v_results_1384_);
if (lean_obj_tag(v_bestResult_x3f_1408_) == 1)
{
lean_object* v___x_1409_; 
lean_dec_ref(v_children_1381_);
lean_dec_ref(v_info_1380_);
lean_dec_ref(v_ctx_1379_);
v___x_1409_ = lean_apply_2(v_toPure_1378_, lean_box(0), v_bestResult_x3f_1408_);
return v___x_1409_;
}
else
{
lean_object* v___x_1410_; uint8_t v___y_1412_; uint8_t v___y_1413_; uint8_t v___y_1414_; uint8_t v___y_1427_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
lean_dec(v_bestResult_x3f_1408_);
v___x_1410_ = l_Lean_Elab_Info_stx(v_info_1380_);
v___x_1432_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__1));
lean_inc(v___x_1410_);
v___x_1433_ = l_Lean_Syntax_isOfKind(v___x_1410_, v___x_1432_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; 
lean_inc_ref(v_info_1380_);
v___x_1434_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_1380_);
if (lean_obj_tag(v___x_1434_) == 0)
{
v___y_1427_ = v___x_1433_;
goto v___jp_1426_;
}
else
{
lean_object* v_val_1435_; lean_object* v_elaborator_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v_val_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_val_1435_);
lean_dec_ref_known(v___x_1434_, 1);
v_elaborator_1436_ = lean_ctor_get(v_val_1435_, 0);
lean_inc(v_elaborator_1436_);
lean_dec(v_val_1435_);
v___x_1437_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6));
v___x_1438_ = lean_name_eq(v_elaborator_1436_, v___x_1437_);
lean_dec(v_elaborator_1436_);
v___y_1427_ = v___x_1438_;
goto v___jp_1426_;
}
}
else
{
v___y_1427_ = v___x_1433_;
goto v___jp_1426_;
}
v___jp_1411_:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_Syntax_getRange_x3f(v___x_1410_, v___y_1412_);
lean_dec(v___x_1410_);
if (lean_obj_tag(v___x_1415_) == 1)
{
lean_object* v_val_1416_; uint8_t v___x_1417_; 
v_val_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_val_1416_);
lean_dec_ref_known(v___x_1415_, 1);
v___x_1417_ = l_Lean_Syntax_Range_contains(v_val_1416_, v_hoverPos_1382_, v_includeStop_1383_);
if (v___x_1417_ == 0)
{
lean_dec(v_val_1416_);
lean_dec_ref(v_children_1381_);
lean_dec_ref(v_info_1380_);
lean_dec_ref(v_ctx_1379_);
goto v___jp_1401_;
}
else
{
if (v___y_1414_ == 0)
{
lean_dec(v_val_1416_);
lean_dec_ref(v_children_1381_);
lean_dec_ref(v_info_1380_);
lean_dec_ref(v_ctx_1379_);
goto v___jp_1401_;
}
else
{
lean_object* v_start_1418_; lean_object* v_stop_1419_; uint8_t v_decide_1420_; lean_object* v___x_1421_; 
v_start_1418_ = lean_ctor_get(v_val_1416_, 0);
lean_inc(v_start_1418_);
v_stop_1419_ = lean_ctor_get(v_val_1416_, 1);
lean_inc(v_stop_1419_);
lean_dec(v_val_1416_);
v_decide_1420_ = lean_nat_dec_eq(v_stop_1419_, v_hoverPos_1382_);
v___x_1421_ = lean_nat_sub(v_stop_1419_, v_start_1418_);
lean_dec(v_start_1418_);
lean_dec(v_stop_1419_);
if (lean_obj_tag(v_info_1380_) == 1)
{
lean_object* v_i_1422_; lean_object* v_expr_1423_; 
v_i_1422_ = lean_ctor_get(v_info_1380_, 0);
v_expr_1423_ = lean_ctor_get(v_i_1422_, 3);
if (lean_obj_tag(v_expr_1423_) == 1)
{
v___y_1396_ = v___y_1412_;
v___y_1397_ = v_decide_1420_;
v___y_1398_ = v___x_1421_;
v___y_1399_ = v___y_1413_;
v___y_1400_ = v___y_1412_;
goto v___jp_1395_;
}
else
{
v___y_1396_ = v___y_1412_;
v___y_1397_ = v_decide_1420_;
v___y_1398_ = v___x_1421_;
v___y_1399_ = v___y_1413_;
v___y_1400_ = v___y_1413_;
goto v___jp_1395_;
}
}
else
{
v___y_1396_ = v___y_1412_;
v___y_1397_ = v_decide_1420_;
v___y_1398_ = v___x_1421_;
v___y_1399_ = v___y_1413_;
v___y_1400_ = v___y_1413_;
goto v___jp_1395_;
}
}
}
}
else
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
lean_dec(v___x_1415_);
lean_dec_ref(v_children_1381_);
lean_dec_ref(v_info_1380_);
lean_dec_ref(v_ctx_1379_);
v___x_1424_ = lean_box(0);
v___x_1425_ = lean_apply_2(v_toPure_1378_, lean_box(0), v___x_1424_);
return v___x_1425_;
}
}
v___jp_1426_:
{
if (v___y_1427_ == 0)
{
uint8_t v___x_1428_; 
v___x_1428_ = 1;
switch(lean_obj_tag(v_info_1380_))
{
case 7:
{
v___y_1412_ = v___x_1428_;
v___y_1413_ = v___y_1427_;
v___y_1414_ = v___x_1428_;
goto v___jp_1411_;
}
case 5:
{
v___y_1412_ = v___x_1428_;
v___y_1413_ = v___y_1427_;
v___y_1414_ = v___x_1428_;
goto v___jp_1411_;
}
case 6:
{
v___y_1412_ = v___x_1428_;
v___y_1413_ = v___y_1427_;
v___y_1414_ = v___x_1428_;
goto v___jp_1411_;
}
default: 
{
lean_object* v___x_1429_; 
lean_inc_ref(v_info_1380_);
v___x_1429_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_1380_);
if (lean_obj_tag(v___x_1429_) == 0)
{
v___y_1412_ = v___x_1428_;
v___y_1413_ = v___y_1427_;
v___y_1414_ = v___y_1427_;
goto v___jp_1411_;
}
else
{
lean_dec_ref_known(v___x_1429_, 1);
v___y_1412_ = v___x_1428_;
v___y_1413_ = v___y_1427_;
v___y_1414_ = v___x_1428_;
goto v___jp_1411_;
}
}
}
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec(v___x_1410_);
lean_dec_ref(v_children_1381_);
lean_dec_ref(v_info_1380_);
lean_dec_ref(v_ctx_1379_);
v___x_1430_ = lean_box(0);
v___x_1431_ = lean_apply_2(v_toPure_1378_, lean_box(0), v___x_1430_);
return v___x_1431_;
}
}
}
v___jp_1385_:
{
lean_object* v_priority_1390_; lean_object* v_result_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v_priority_1390_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_priority_1390_, 0, v___y_1388_);
lean_ctor_set_uint8(v_priority_1390_, sizeof(void*)*1, v___y_1387_);
lean_ctor_set_uint8(v_priority_1390_, sizeof(void*)*1 + 1, v___y_1386_);
lean_ctor_set_uint8(v_priority_1390_, sizeof(void*)*1 + 2, v___y_1389_);
v_result_1391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_result_1391_, 0, v_ctx_1379_);
lean_ctor_set(v_result_1391_, 1, v_info_1380_);
lean_ctor_set(v_result_1391_, 2, v_children_1381_);
v___x_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1392_, 0, v_priority_1390_);
lean_ctor_set(v___x_1392_, 1, v_result_1391_);
v___x_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
v___x_1394_ = lean_apply_2(v_toPure_1378_, lean_box(0), v___x_1393_);
return v___x_1394_;
}
v___jp_1395_:
{
if (lean_obj_tag(v_info_1380_) == 2)
{
v___y_1386_ = v___y_1400_;
v___y_1387_ = v___y_1397_;
v___y_1388_ = v___y_1398_;
v___y_1389_ = v___y_1396_;
goto v___jp_1385_;
}
else
{
v___y_1386_ = v___y_1400_;
v___y_1387_ = v___y_1397_;
v___y_1388_ = v___y_1398_;
v___y_1389_ = v___y_1399_;
goto v___jp_1385_;
}
}
v___jp_1401_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = lean_box(0);
v___x_1403_ = lean_apply_2(v_toPure_1378_, lean_box(0), v___x_1402_);
return v___x_1403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___boxed(lean_object* v___f_1439_, lean_object* v___f_1440_, lean_object* v___x_1441_, lean_object* v_toPure_1442_, lean_object* v_ctx_1443_, lean_object* v_info_1444_, lean_object* v_children_1445_, lean_object* v_hoverPos_1446_, lean_object* v_includeStop_1447_, lean_object* v_results_1448_){
_start:
{
uint8_t v_includeStop_boxed_1449_; lean_object* v_res_1450_; 
v_includeStop_boxed_1449_ = lean_unbox(v_includeStop_1447_);
v_res_1450_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3(v___f_1439_, v___f_1440_, v___x_1441_, v_toPure_1442_, v_ctx_1443_, v_info_1444_, v_children_1445_, v_hoverPos_1446_, v_includeStop_boxed_1449_, v_results_1448_);
lean_dec(v_hoverPos_1446_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4(lean_object* v___f_1453_, lean_object* v___f_1454_, lean_object* v___x_1455_, lean_object* v_toPure_1456_, lean_object* v_hoverPos_1457_, uint8_t v_includeStop_1458_, lean_object* v___f_1459_, lean_object* v_filter_1460_, lean_object* v_toBind_1461_, lean_object* v_ctx_1462_, lean_object* v_info_1463_, lean_object* v_children_1464_, lean_object* v_results_1465_){
_start:
{
lean_object* v___x_1466_; lean_object* v___f_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1466_ = lean_box(v_includeStop_1458_);
lean_inc_ref(v_children_1464_);
lean_inc_ref(v_info_1463_);
lean_inc_ref(v_ctx_1462_);
v___f_1467_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_1467_, 0, v___f_1453_);
lean_closure_set(v___f_1467_, 1, v___f_1454_);
lean_closure_set(v___f_1467_, 2, v___x_1455_);
lean_closure_set(v___f_1467_, 3, v_toPure_1456_);
lean_closure_set(v___f_1467_, 4, v_ctx_1462_);
lean_closure_set(v___f_1467_, 5, v_info_1463_);
lean_closure_set(v___f_1467_, 6, v_children_1464_);
lean_closure_set(v___f_1467_, 7, v_hoverPos_1457_);
lean_closure_set(v___f_1467_, 8, v___x_1466_);
v___x_1468_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___closed__0));
v___x_1469_ = l_List_filterMapTR_go___redArg(v___f_1459_, v_results_1465_, v___x_1468_);
v___x_1470_ = lean_apply_4(v_filter_1460_, v_ctx_1462_, v_info_1463_, v_children_1464_, v___x_1469_);
v___x_1471_ = lean_apply_4(v_toBind_1461_, lean_box(0), lean_box(0), v___x_1470_, v___f_1467_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___boxed(lean_object* v___f_1472_, lean_object* v___f_1473_, lean_object* v___x_1474_, lean_object* v_toPure_1475_, lean_object* v_hoverPos_1476_, lean_object* v_includeStop_1477_, lean_object* v___f_1478_, lean_object* v_filter_1479_, lean_object* v_toBind_1480_, lean_object* v_ctx_1481_, lean_object* v_info_1482_, lean_object* v_children_1483_, lean_object* v_results_1484_){
_start:
{
uint8_t v_includeStop_boxed_1485_; lean_object* v_res_1486_; 
v_includeStop_boxed_1485_ = lean_unbox(v_includeStop_1477_);
v_res_1486_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4(v___f_1472_, v___f_1473_, v___x_1474_, v_toPure_1475_, v_hoverPos_1476_, v_includeStop_boxed_1485_, v___f_1478_, v_filter_1479_, v_toBind_1480_, v_ctx_1481_, v_info_1482_, v_children_1483_, v_results_1484_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__6(lean_object* v_toPure_1487_, lean_object* v_results_1488_){
_start:
{
if (lean_obj_tag(v_results_1488_) == 0)
{
goto v___jp_1489_;
}
else
{
lean_object* v_val_1492_; 
v_val_1492_ = lean_ctor_get(v_results_1488_, 0);
lean_inc(v_val_1492_);
lean_dec_ref_known(v_results_1488_, 1);
if (lean_obj_tag(v_val_1492_) == 0)
{
goto v___jp_1489_;
}
else
{
lean_object* v_val_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1509_; 
v_val_1493_ = lean_ctor_get(v_val_1492_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_val_1492_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1495_ = v_val_1492_;
v_isShared_1496_ = v_isSharedCheck_1509_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_val_1493_);
lean_dec(v_val_1492_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1509_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v_snd_1497_; lean_object* v_info_1498_; lean_object* v___x_1500_; 
v_snd_1497_ = lean_ctor_get(v_val_1493_, 1);
lean_inc(v_snd_1497_);
lean_dec(v_val_1493_);
v_info_1498_ = lean_ctor_get(v_snd_1497_, 1);
lean_inc_ref(v_info_1498_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v_snd_1497_);
v___x_1500_ = v___x_1495_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_snd_1497_);
v___x_1500_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
if (lean_obj_tag(v_info_1498_) == 1)
{
lean_object* v_i_1501_; lean_object* v_expr_1502_; uint8_t v___x_1503_; 
v_i_1501_ = lean_ctor_get(v_info_1498_, 0);
lean_inc_ref(v_i_1501_);
lean_dec_ref_known(v_info_1498_, 1);
v_expr_1502_ = lean_ctor_get(v_i_1501_, 3);
lean_inc_ref(v_expr_1502_);
lean_dec_ref(v_i_1501_);
v___x_1503_ = l_Lean_Expr_isSyntheticSorry(v_expr_1502_);
lean_dec_ref(v_expr_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_apply_2(v_toPure_1487_, lean_box(0), v___x_1500_);
return v___x_1504_;
}
else
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
lean_dec_ref(v___x_1500_);
v___x_1505_ = lean_box(0);
v___x_1506_ = lean_apply_2(v_toPure_1487_, lean_box(0), v___x_1505_);
return v___x_1506_;
}
}
else
{
lean_object* v___x_1507_; 
lean_dec_ref(v_info_1498_);
v___x_1507_ = lean_apply_2(v_toPure_1487_, lean_box(0), v___x_1500_);
return v___x_1507_;
}
}
}
}
}
v___jp_1489_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = lean_box(0);
v___x_1491_ = lean_apply_2(v_toPure_1487_, lean_box(0), v___x_1490_);
return v___x_1491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg(lean_object* v_inst_1512_, lean_object* v_t_1513_, lean_object* v_hoverPos_1514_, uint8_t v_includeStop_1515_, lean_object* v_filter_1516_){
_start:
{
lean_object* v_toApplicative_1517_; lean_object* v_toBind_1518_; lean_object* v_toPure_1519_; lean_object* v___f_1520_; lean_object* v___f_1521_; lean_object* v___f_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v_postNode_1525_; lean_object* v___f_1526_; lean_object* v___f_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v_toApplicative_1517_ = lean_ctor_get(v_inst_1512_, 0);
v_toBind_1518_ = lean_ctor_get(v_inst_1512_, 1);
lean_inc_n(v_toBind_1518_, 2);
v_toPure_1519_ = lean_ctor_get(v_toApplicative_1517_, 1);
v___f_1520_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__0));
v___f_1521_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__1));
v___f_1522_ = ((lean_object*)(l_Lean_Elab_instMaxHoverableInfoPrio___closed__0));
v___x_1523_ = ((lean_object*)(l_Lean_Elab_instBEqHoverableInfoPrio___closed__0));
v___x_1524_ = lean_box(v_includeStop_1515_);
lean_inc_n(v_toPure_1519_, 3);
v_postNode_1525_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___boxed), 13, 9);
lean_closure_set(v_postNode_1525_, 0, v___f_1520_);
lean_closure_set(v_postNode_1525_, 1, v___f_1522_);
lean_closure_set(v_postNode_1525_, 2, v___x_1523_);
lean_closure_set(v_postNode_1525_, 3, v_toPure_1519_);
lean_closure_set(v_postNode_1525_, 4, v_hoverPos_1514_);
lean_closure_set(v_postNode_1525_, 5, v___x_1524_);
lean_closure_set(v_postNode_1525_, 6, v___f_1521_);
lean_closure_set(v_postNode_1525_, 7, v_filter_1516_);
lean_closure_set(v_postNode_1525_, 8, v_toBind_1518_);
v___f_1526_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__2___boxed), 4, 1);
lean_closure_set(v___f_1526_, 0, v_toPure_1519_);
v___f_1527_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__6), 2, 1);
lean_closure_set(v___f_1527_, 0, v_toPure_1519_);
v___x_1528_ = lean_box(0);
v___x_1529_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_1512_, v___f_1526_, v_postNode_1525_, v___x_1528_, v_t_1513_);
v___x_1530_ = lean_apply_4(v_toBind_1518_, lean_box(0), lean_box(0), v___x_1529_, v___f_1527_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___boxed(lean_object* v_inst_1531_, lean_object* v_t_1532_, lean_object* v_hoverPos_1533_, lean_object* v_includeStop_1534_, lean_object* v_filter_1535_){
_start:
{
uint8_t v_includeStop_boxed_1536_; lean_object* v_res_1537_; 
v_includeStop_boxed_1536_ = lean_unbox(v_includeStop_1534_);
v_res_1537_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg(v_inst_1531_, v_t_1532_, v_hoverPos_1533_, v_includeStop_boxed_1536_, v_filter_1535_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f(lean_object* v_m_1538_, lean_object* v_inst_1539_, lean_object* v_t_1540_, lean_object* v_hoverPos_1541_, uint8_t v_includeStop_1542_, lean_object* v_filter_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg(v_inst_1539_, v_t_1540_, v_hoverPos_1541_, v_includeStop_1542_, v_filter_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___boxed(lean_object* v_m_1545_, lean_object* v_inst_1546_, lean_object* v_t_1547_, lean_object* v_hoverPos_1548_, lean_object* v_includeStop_1549_, lean_object* v_filter_1550_){
_start:
{
uint8_t v_includeStop_boxed_1551_; lean_object* v_res_1552_; 
v_includeStop_boxed_1551_ = lean_unbox(v_includeStop_1549_);
v_res_1552_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f(v_m_1545_, v_inst_1546_, v_t_1547_, v_hoverPos_1548_, v_includeStop_boxed_1551_, v_filter_1550_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_type_x3f(lean_object* v_i_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
switch(lean_obj_tag(v_i_1553_))
{
case 1:
{
lean_object* v_i_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1584_; 
v_i_1559_ = lean_ctor_get(v_i_1553_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_i_1553_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1561_ = v_i_1553_;
v_isShared_1562_ = v_isSharedCheck_1584_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_i_1559_);
lean_dec(v_i_1553_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1584_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v_expr_1563_; lean_object* v___x_1564_; 
v_expr_1563_ = lean_ctor_get(v_i_1559_, 3);
lean_inc_ref(v_expr_1563_);
lean_dec_ref(v_i_1559_);
lean_inc(v_a_1557_);
lean_inc_ref(v_a_1556_);
lean_inc(v_a_1555_);
lean_inc_ref(v_a_1554_);
v___x_1564_ = lean_infer_type(v_expr_1563_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1575_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1567_ = v___x_1564_;
v_isShared_1568_ = v_isSharedCheck_1575_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1564_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1575_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v_a_1565_);
v___x_1570_ = v___x_1561_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
lean_object* v___x_1572_; 
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v___x_1570_);
v___x_1572_ = v___x_1567_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_del_object(v___x_1561_);
v_a_1576_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1564_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1564_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
}
case 7:
{
lean_object* v_i_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1610_; 
v_i_1585_ = lean_ctor_get(v_i_1553_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_i_1553_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1587_ = v_i_1553_;
v_isShared_1588_ = v_isSharedCheck_1610_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_i_1585_);
lean_dec(v_i_1553_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1610_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v_val_1589_; lean_object* v___x_1590_; 
v_val_1589_ = lean_ctor_get(v_i_1585_, 3);
lean_inc_ref(v_val_1589_);
lean_dec_ref(v_i_1585_);
lean_inc(v_a_1557_);
lean_inc_ref(v_a_1556_);
lean_inc(v_a_1555_);
lean_inc_ref(v_a_1554_);
v___x_1590_ = lean_infer_type(v_val_1589_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1601_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1601_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1601_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1588_ == 0)
{
lean_ctor_set_tag(v___x_1587_, 1);
lean_ctor_set(v___x_1587_, 0, v_a_1591_);
v___x_1596_ = v___x_1587_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1598_; 
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v___x_1596_);
v___x_1598_ = v___x_1593_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_del_object(v___x_1587_);
v_a_1602_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1590_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1590_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
case 13:
{
lean_object* v_i_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1637_; 
v_i_1611_ = lean_ctor_get(v_i_1553_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_i_1553_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1613_ = v_i_1553_;
v_isShared_1614_ = v_isSharedCheck_1637_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_i_1611_);
lean_dec(v_i_1553_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1637_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v_toTermInfo_1615_; lean_object* v_expr_1616_; lean_object* v___x_1617_; 
v_toTermInfo_1615_ = lean_ctor_get(v_i_1611_, 0);
lean_inc_ref(v_toTermInfo_1615_);
lean_dec_ref(v_i_1611_);
v_expr_1616_ = lean_ctor_get(v_toTermInfo_1615_, 3);
lean_inc_ref(v_expr_1616_);
lean_dec_ref(v_toTermInfo_1615_);
lean_inc(v_a_1557_);
lean_inc_ref(v_a_1556_);
lean_inc(v_a_1555_);
lean_inc_ref(v_a_1554_);
v___x_1617_ = lean_infer_type(v_expr_1616_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1628_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1628_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1628_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1614_ == 0)
{
lean_ctor_set_tag(v___x_1613_, 1);
lean_ctor_set(v___x_1613_, 0, v_a_1618_);
v___x_1623_ = v___x_1613_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1625_; 
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v___x_1623_);
v___x_1625_ = v___x_1620_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1623_);
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
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_del_object(v___x_1613_);
v_a_1629_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1617_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1617_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
default: 
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_dec_ref(v_i_1553_);
v___x_1638_ = lean_box(0);
v___x_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
return v___x_1639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_type_x3f___boxed(lean_object* v_i_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_Elab_Info_type_x3f(v_i_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_);
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
lean_dec(v_a_1642_);
lean_dec_ref(v_a_1641_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(lean_object* v_declName_1647_, uint8_t v_includeBuiltin_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1652_; lean_object* v_toCold_1653_; lean_object* v_env_1654_; lean_object* v_ref_1655_; lean_object* v_currNamespace_1656_; lean_object* v_openDecls_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1652_ = lean_st_ref_get(v___y_1650_);
v_toCold_1653_ = lean_ctor_get(v___y_1649_, 0);
v_env_1654_ = lean_ctor_get(v___x_1652_, 0);
lean_inc_ref(v_env_1654_);
lean_dec(v___x_1652_);
v_ref_1655_ = lean_ctor_get(v___y_1649_, 2);
v_currNamespace_1656_ = lean_ctor_get(v_toCold_1653_, 4);
v_openDecls_1657_ = lean_ctor_get(v_toCold_1653_, 5);
v___x_1658_ = l_Lean_Options_empty;
lean_inc(v_openDecls_1657_);
lean_inc(v_currNamespace_1656_);
v___x_1659_ = l_Lean_findDocString_x3f(v_env_1654_, v_declName_1647_, v_includeBuiltin_1648_, v___x_1658_, v_currNamespace_1656_, v_openDecls_1657_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1679_; 
v_a_1668_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1670_ = v___x_1659_;
v_isShared_1671_ = v_isSharedCheck_1679_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1659_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1679_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1672_ = lean_io_error_to_string(v_a_1668_);
v___x_1673_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
v___x_1674_ = l_Lean_MessageData_ofFormat(v___x_1673_);
lean_inc(v_ref_1655_);
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v_ref_1655_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1675_);
v___x_1677_ = v___x_1670_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg___boxed(lean_object* v_declName_1680_, lean_object* v_includeBuiltin_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
uint8_t v_includeBuiltin_boxed_1685_; lean_object* v_res_1686_; 
v_includeBuiltin_boxed_1685_ = lean_unbox(v_includeBuiltin_1681_);
v_res_1686_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_declName_1680_, v_includeBuiltin_boxed_1685_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0(lean_object* v_declName_1687_, uint8_t v_includeBuiltin_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_declName_1687_, v_includeBuiltin_1688_, v___y_1691_, v___y_1692_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___boxed(lean_object* v_declName_1695_, lean_object* v_includeBuiltin_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
uint8_t v_includeBuiltin_boxed_1702_; lean_object* v_res_1703_; 
v_includeBuiltin_boxed_1702_ = lean_unbox(v_includeBuiltin_1696_);
v_res_1703_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0(v_declName_1695_, v_includeBuiltin_boxed_1702_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg(lean_object* v_name_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v_env_1709_; lean_object* v___x_1710_; lean_object* v_toEnvExtension_1711_; lean_object* v_asyncMode_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1707_ = lean_box(1);
v___x_1708_ = lean_st_ref_get(v___y_1705_);
v_env_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc_ref(v_env_1709_);
lean_dec(v___x_1708_);
v___x_1710_ = l_Lean_errorExplanationExt;
v_toEnvExtension_1711_ = lean_ctor_get(v___x_1710_, 0);
v_asyncMode_1712_ = lean_ctor_get(v_toEnvExtension_1711_, 2);
v___x_1713_ = lean_box(0);
v___x_1714_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1707_, v___x_1710_, v_env_1709_, v_asyncMode_1712_, v___x_1713_);
v___x_1715_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1714_, v_name_1704_);
lean_dec(v___x_1714_);
v___x_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg___boxed(lean_object* v_name_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg(v_name_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec(v_name_1717_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1(lean_object* v_name_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg(v_name_1721_, v___y_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___boxed(lean_object* v_name_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1(v_name_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v_name_1728_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_docString_x3f(lean_object* v_i_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; 
switch(lean_obj_tag(v_i_1735_))
{
case 1:
{
lean_object* v_i_1757_; lean_object* v_expr_1758_; lean_object* v___x_1759_; 
v_i_1757_ = lean_ctor_get(v_i_1735_, 0);
v_expr_1758_ = lean_ctor_get(v_i_1757_, 3);
v___x_1759_ = l_Lean_Expr_constName_x3f(v_expr_1758_);
if (lean_obj_tag(v___x_1759_) == 1)
{
lean_object* v_val_1760_; uint8_t v___x_1761_; lean_object* v___x_1762_; 
lean_dec_ref_known(v_i_1735_, 1);
v_val_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_val_1760_);
lean_dec_ref_known(v___x_1759_, 1);
v___x_1761_ = 1;
v___x_1762_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_val_1760_, v___x_1761_, v_a_1738_, v_a_1739_);
return v___x_1762_;
}
else
{
lean_dec(v___x_1759_);
v___y_1742_ = v_a_1736_;
v___y_1743_ = v_a_1737_;
v___y_1744_ = v_a_1738_;
v___y_1745_ = v_a_1739_;
goto v___jp_1741_;
}
}
case 13:
{
lean_object* v_i_1763_; lean_object* v___x_1764_; 
v_i_1763_ = lean_ctor_get(v_i_1735_, 0);
v___x_1764_ = l_Lean_Meta_getPPContext(v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v_ref_1766_; lean_object* v___x_1767_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v_ref_1766_ = lean_ctor_get(v_a_1738_, 2);
lean_inc_ref(v_i_1763_);
v___x_1767_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v_a_1765_, v_i_1763_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1781_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1770_ = v___x_1767_;
v_isShared_1771_ = v_isSharedCheck_1781_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1767_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1781_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
if (lean_obj_tag(v_a_1768_) == 1)
{
lean_object* v___x_1773_; 
lean_dec_ref_known(v_i_1735_, 1);
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
else
{
lean_object* v_toTermInfo_1775_; lean_object* v_expr_1776_; lean_object* v___x_1777_; 
lean_del_object(v___x_1770_);
lean_dec(v_a_1768_);
v_toTermInfo_1775_ = lean_ctor_get(v_i_1763_, 0);
v_expr_1776_ = lean_ctor_get(v_toTermInfo_1775_, 3);
v___x_1777_ = l_Lean_Expr_constName_x3f(v_expr_1776_);
if (lean_obj_tag(v___x_1777_) == 1)
{
lean_object* v_val_1778_; uint8_t v___x_1779_; lean_object* v___x_1780_; 
lean_dec_ref_known(v_i_1735_, 1);
v_val_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_val_1778_);
lean_dec_ref_known(v___x_1777_, 1);
v___x_1779_ = 1;
v___x_1780_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_val_1778_, v___x_1779_, v_a_1738_, v_a_1739_);
return v___x_1780_;
}
else
{
lean_dec(v___x_1777_);
v___y_1742_ = v_a_1736_;
v___y_1743_ = v_a_1737_;
v___y_1744_ = v_a_1738_;
v___y_1745_ = v_a_1739_;
goto v___jp_1741_;
}
}
}
}
else
{
lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1799_; 
v_isSharedCheck_1799_ = !lean_is_exclusive(v_i_1735_);
if (v_isSharedCheck_1799_ == 0)
{
lean_object* v_unused_1800_; 
v_unused_1800_ = lean_ctor_get(v_i_1735_, 0);
lean_dec(v_unused_1800_);
v___x_1783_ = v_i_1735_;
v_isShared_1784_ = v_isSharedCheck_1799_;
goto v_resetjp_1782_;
}
else
{
lean_dec(v_i_1735_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1799_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1798_; 
v_a_1785_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1787_ = v___x_1767_;
v_isShared_1788_ = v_isSharedCheck_1798_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1767_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1798_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; lean_object* v___x_1791_; 
v___x_1789_ = lean_io_error_to_string(v_a_1785_);
if (v_isShared_1784_ == 0)
{
lean_ctor_set_tag(v___x_1783_, 3);
lean_ctor_set(v___x_1783_, 0, v___x_1789_);
v___x_1791_ = v___x_1783_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1792_ = l_Lean_MessageData_ofFormat(v___x_1791_);
lean_inc(v_ref_1766_);
v___x_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1793_, 0, v_ref_1766_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v___x_1793_);
v___x_1795_ = v___x_1787_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec_ref_known(v_i_1735_, 1);
v_a_1801_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1764_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1764_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
case 7:
{
lean_object* v_i_1809_; lean_object* v_projName_1810_; uint8_t v___x_1811_; lean_object* v___x_1812_; 
v_i_1809_ = lean_ctor_get(v_i_1735_, 0);
lean_inc_ref(v_i_1809_);
lean_dec_ref_known(v_i_1735_, 1);
v_projName_1810_ = lean_ctor_get(v_i_1809_, 0);
lean_inc(v_projName_1810_);
lean_dec_ref(v_i_1809_);
v___x_1811_ = 1;
v___x_1812_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_projName_1810_, v___x_1811_, v_a_1738_, v_a_1739_);
return v___x_1812_;
}
case 5:
{
lean_object* v_i_1813_; lean_object* v_optionName_1814_; lean_object* v_declName_1815_; uint8_t v___x_1816_; lean_object* v___x_1817_; 
v_i_1813_ = lean_ctor_get(v_i_1735_, 0);
lean_inc_ref(v_i_1813_);
lean_dec_ref_known(v_i_1735_, 1);
v_optionName_1814_ = lean_ctor_get(v_i_1813_, 1);
lean_inc(v_optionName_1814_);
v_declName_1815_ = lean_ctor_get(v_i_1813_, 2);
lean_inc(v_declName_1815_);
lean_dec_ref(v_i_1813_);
v___x_1816_ = 1;
v___x_1817_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_declName_1815_, v___x_1816_, v_a_1738_, v_a_1739_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1818_);
if (lean_obj_tag(v_a_1818_) == 1)
{
lean_dec_ref_known(v_a_1818_, 1);
lean_dec(v_optionName_1814_);
return v___x_1817_;
}
else
{
lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1860_; 
lean_dec(v_a_1818_);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1860_ == 0)
{
lean_object* v_unused_1861_; 
v_unused_1861_ = lean_ctor_get(v___x_1817_, 0);
lean_dec(v_unused_1861_);
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1860_;
goto v_resetjp_1819_;
}
else
{
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1860_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v_ref_1822_; lean_object* v___x_1823_; 
v_ref_1822_ = lean_ctor_get(v_a_1738_, 2);
v___x_1823_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1845_; 
lean_del_object(v___x_1820_);
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1826_ = v___x_1823_;
v_isShared_1827_ = v_isSharedCheck_1845_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1823_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1845_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1824_, v_optionName_1814_);
lean_dec(v_optionName_1814_);
lean_dec(v_a_1824_);
if (lean_obj_tag(v___x_1828_) == 1)
{
lean_object* v_val_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1840_; 
v_val_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1840_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_val_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1840_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1833_ = l_Lean_OptionDecl_fullDescr(v_val_1829_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1833_);
v___x_1835_ = v___x_1831_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1837_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v___x_1835_);
v___x_1837_ = v___x_1826_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
else
{
lean_object* v___x_1841_; lean_object* v___x_1843_; 
lean_dec(v___x_1828_);
v___x_1841_ = lean_box(0);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v___x_1841_);
v___x_1843_ = v___x_1826_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1859_; 
lean_dec(v_optionName_1814_);
v_a_1846_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1848_ = v___x_1823_;
v_isShared_1849_ = v_isSharedCheck_1859_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1823_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1859_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1850_ = lean_io_error_to_string(v_a_1846_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set_tag(v___x_1820_, 3);
lean_ctor_set(v___x_1820_, 0, v___x_1850_);
v___x_1852_ = v___x_1820_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1853_ = l_Lean_MessageData_ofFormat(v___x_1852_);
lean_inc(v_ref_1822_);
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v_ref_1822_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v___x_1854_);
v___x_1856_ = v___x_1848_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
}
}
else
{
lean_dec(v_optionName_1814_);
return v___x_1817_;
}
}
case 6:
{
lean_object* v_i_1862_; lean_object* v_errorName_1863_; lean_object* v___x_1864_; lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1885_; 
v_i_1862_ = lean_ctor_get(v_i_1735_, 0);
lean_inc_ref(v_i_1862_);
lean_dec_ref_known(v_i_1735_, 1);
v_errorName_1863_ = lean_ctor_get(v_i_1862_, 1);
lean_inc(v_errorName_1863_);
lean_dec_ref(v_i_1862_);
v___x_1864_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg(v_errorName_1863_, v_a_1739_);
lean_dec(v_errorName_1863_);
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1867_ = v___x_1864_;
v_isShared_1868_ = v_isSharedCheck_1885_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1864_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1885_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
if (lean_obj_tag(v_a_1865_) == 1)
{
lean_object* v_val_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1880_; 
v_val_1869_ = lean_ctor_get(v_a_1865_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_a_1865_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1871_ = v_a_1865_;
v_isShared_1872_ = v_isSharedCheck_1880_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_val_1869_);
lean_dec(v_a_1865_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1880_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v___x_1875_; 
v___x_1873_ = l_Lean_ErrorExplanation_summaryWithSeverity(v_val_1869_);
lean_dec(v_val_1869_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1873_);
v___x_1875_ = v___x_1871_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1873_);
v___x_1875_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1877_; 
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v___x_1875_);
v___x_1877_ = v___x_1867_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
else
{
lean_object* v___x_1881_; lean_object* v___x_1883_; 
lean_dec(v_a_1865_);
v___x_1881_ = lean_box(0);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v___x_1881_);
v___x_1883_ = v___x_1867_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
case 16:
{
lean_object* v_i_1886_; lean_object* v_stx_1887_; lean_object* v___x_1888_; uint8_t v___x_1889_; lean_object* v___x_1890_; 
v_i_1886_ = lean_ctor_get(v_i_1735_, 0);
lean_inc_ref(v_i_1886_);
lean_dec_ref_known(v_i_1735_, 1);
v_stx_1887_ = lean_ctor_get(v_i_1886_, 1);
lean_inc(v_stx_1887_);
lean_dec_ref(v_i_1886_);
v___x_1888_ = l_Lean_Syntax_getKind(v_stx_1887_);
v___x_1889_ = 1;
v___x_1890_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v___x_1888_, v___x_1889_, v_a_1738_, v_a_1739_);
return v___x_1890_;
}
case 17:
{
lean_object* v_i_1891_; lean_object* v_name_1892_; uint8_t v___x_1893_; lean_object* v___x_1894_; 
v_i_1891_ = lean_ctor_get(v_i_1735_, 0);
lean_inc_ref(v_i_1891_);
lean_dec_ref_known(v_i_1735_, 1);
v_name_1892_ = lean_ctor_get(v_i_1891_, 1);
lean_inc(v_name_1892_);
lean_dec_ref(v_i_1891_);
v___x_1893_ = 1;
v___x_1894_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_name_1892_, v___x_1893_, v_a_1738_, v_a_1739_);
return v___x_1894_;
}
default: 
{
v___y_1742_ = v_a_1736_;
v___y_1743_ = v_a_1737_;
v___y_1744_ = v_a_1738_;
v___y_1745_ = v_a_1739_;
goto v___jp_1741_;
}
}
v___jp_1741_:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_Elab_Info_toElabInfo_x3f(v_i_1735_);
if (lean_obj_tag(v___x_1746_) == 1)
{
lean_object* v_val_1747_; lean_object* v_elaborator_1748_; lean_object* v_stx_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; lean_object* v___x_1752_; 
v_val_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_val_1747_);
lean_dec_ref_known(v___x_1746_, 1);
v_elaborator_1748_ = lean_ctor_get(v_val_1747_, 0);
lean_inc(v_elaborator_1748_);
v_stx_1749_ = lean_ctor_get(v_val_1747_, 1);
lean_inc(v_stx_1749_);
lean_dec(v_val_1747_);
v___x_1750_ = l_Lean_Syntax_getKind(v_stx_1749_);
v___x_1751_ = 1;
v___x_1752_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v___x_1750_, v___x_1751_, v___y_1744_, v___y_1745_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
if (lean_obj_tag(v_a_1753_) == 0)
{
lean_object* v___x_1754_; 
lean_dec_ref_known(v___x_1752_, 1);
v___x_1754_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_elaborator_1748_, v___x_1751_, v___y_1744_, v___y_1745_);
return v___x_1754_;
}
else
{
lean_dec_ref_known(v_a_1753_, 1);
lean_dec(v_elaborator_1748_);
return v___x_1752_;
}
}
else
{
lean_dec(v_elaborator_1748_);
return v___x_1752_;
}
}
else
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_dec(v___x_1746_);
v___x_1755_ = lean_box(0);
v___x_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
return v___x_1756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_docString_x3f___boxed(lean_object* v_i_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_Elab_Info_docString_x3f(v_i_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
return v_res_1901_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1902_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
return v___x_1904_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1905_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1906_ = lean_unsigned_to_nat(0u);
v___x_1907_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
lean_ctor_set(v___x_1907_, 2, v___x_1906_);
lean_ctor_set(v___x_1907_, 3, v___x_1906_);
lean_ctor_set(v___x_1907_, 4, v___x_1905_);
lean_ctor_set(v___x_1907_, 5, v___x_1905_);
lean_ctor_set(v___x_1907_, 6, v___x_1905_);
lean_ctor_set(v___x_1907_, 7, v___x_1905_);
lean_ctor_set(v___x_1907_, 8, v___x_1905_);
lean_ctor_set(v___x_1907_, 9, v___x_1905_);
lean_ctor_set(v___x_1907_, 10, v___x_1905_);
return v___x_1907_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1908_ = lean_unsigned_to_nat(32u);
v___x_1909_ = lean_mk_empty_array_with_capacity(v___x_1908_);
v___x_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
return v___x_1910_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1911_ = ((size_t)5ULL);
v___x_1912_ = lean_unsigned_to_nat(0u);
v___x_1913_ = lean_unsigned_to_nat(32u);
v___x_1914_ = lean_mk_empty_array_with_capacity(v___x_1913_);
v___x_1915_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1916_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
lean_ctor_set(v___x_1916_, 1, v___x_1914_);
lean_ctor_set(v___x_1916_, 2, v___x_1912_);
lean_ctor_set(v___x_1916_, 3, v___x_1912_);
lean_ctor_set_usize(v___x_1916_, 4, v___x_1911_);
return v___x_1916_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1917_ = lean_box(1);
v___x_1918_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_1919_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1920_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
lean_ctor_set(v___x_1920_, 1, v___x_1918_);
lean_ctor_set(v___x_1920_, 2, v___x_1917_);
return v___x_1920_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1923_ = l_Lean_stringToMessageData(v___x_1922_);
return v___x_1923_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1926_ = l_Lean_stringToMessageData(v___x_1925_);
return v___x_1926_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1929_ = l_Lean_stringToMessageData(v___x_1928_);
return v___x_1929_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1932_ = l_Lean_stringToMessageData(v___x_1931_);
return v___x_1932_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_1935_ = l_Lean_stringToMessageData(v___x_1934_);
return v___x_1935_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_1938_ = l_Lean_stringToMessageData(v___x_1937_);
return v___x_1938_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_1941_ = l_Lean_stringToMessageData(v___x_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1942_, lean_object* v_declHint_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v_env_1948_; uint8_t v___x_1949_; 
v___x_1946_ = lean_box(0);
v___x_1947_ = lean_st_ref_get(v___y_1944_);
v_env_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc_ref(v_env_1948_);
lean_dec(v___x_1947_);
v___x_1949_ = l_Lean_Name_isAnonymous(v_declHint_1943_);
if (v___x_1949_ == 0)
{
uint8_t v_isExporting_1950_; 
v_isExporting_1950_ = lean_ctor_get_uint8(v_env_1948_, sizeof(void*)*8);
if (v_isExporting_1950_ == 0)
{
lean_object* v___x_1951_; 
lean_dec_ref(v_env_1948_);
lean_dec(v_declHint_1943_);
v___x_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1951_, 0, v_msg_1942_);
return v___x_1951_;
}
else
{
lean_object* v___x_1952_; uint8_t v___x_1953_; 
lean_inc_ref(v_env_1948_);
v___x_1952_ = l_Lean_Environment_setExporting(v_env_1948_, v___x_1949_);
lean_inc(v_declHint_1943_);
lean_inc_ref(v___x_1952_);
v___x_1953_ = l_Lean_Environment_contains(v___x_1952_, v_declHint_1943_, v_isExporting_1950_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; 
lean_dec_ref(v___x_1952_);
lean_dec_ref(v_env_1948_);
lean_dec(v_declHint_1943_);
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v_msg_1942_);
return v___x_1954_;
}
else
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v_c_1960_; lean_object* v___x_1961_; 
v___x_1955_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_1956_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1957_ = l_Lean_Options_empty;
v___x_1958_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1952_);
lean_ctor_set(v___x_1958_, 1, v___x_1955_);
lean_ctor_set(v___x_1958_, 2, v___x_1956_);
lean_ctor_set(v___x_1958_, 3, v___x_1957_);
lean_inc(v_declHint_1943_);
v___x_1959_ = l_Lean_MessageData_ofConstName(v_declHint_1943_, v___x_1949_);
v_c_1960_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1960_, 0, v___x_1958_);
lean_ctor_set(v_c_1960_, 1, v___x_1959_);
v___x_1961_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1948_, v_declHint_1943_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
lean_dec_ref(v_env_1948_);
lean_dec(v_declHint_1943_);
v___x_1962_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
lean_ctor_set(v___x_1963_, 1, v_c_1960_);
v___x_1964_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1963_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = l_Lean_MessageData_note(v___x_1965_);
v___x_1967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1967_, 0, v_msg_1942_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v___x_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
return v___x_1968_;
}
else
{
lean_object* v_val_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_2003_; 
v_val_1969_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1971_ = v___x_1961_;
v_isShared_1972_ = v_isSharedCheck_2003_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_val_1969_);
lean_dec(v___x_1961_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_2003_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v_mod_1975_; uint8_t v___x_1976_; 
v___x_1973_ = l_Lean_Environment_header(v_env_1948_);
lean_dec_ref(v_env_1948_);
v___x_1974_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1973_);
v_mod_1975_ = lean_array_get(v___x_1946_, v___x_1974_, v_val_1969_);
lean_dec(v_val_1969_);
lean_dec_ref(v___x_1974_);
v___x_1976_ = l_Lean_isPrivateName(v_declHint_1943_);
lean_dec(v_declHint_1943_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1977_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
lean_ctor_set(v___x_1978_, 1, v_c_1960_);
v___x_1979_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1978_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = l_Lean_MessageData_ofName(v_mod_1975_);
v___x_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1980_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_1984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1982_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = l_Lean_MessageData_note(v___x_1984_);
v___x_1986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1986_, 0, v_msg_1942_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set_tag(v___x_1971_, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1986_);
v___x_1988_ = v___x_1971_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
else
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1990_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
lean_ctor_set(v___x_1991_, 1, v_c_1960_);
v___x_1992_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_1993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = l_Lean_MessageData_ofName(v_mod_1975_);
v___x_1995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1993_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_1997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1995_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
v___x_1998_ = l_Lean_MessageData_note(v___x_1997_);
v___x_1999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1999_, 0, v_msg_1942_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set_tag(v___x_1971_, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1999_);
v___x_2001_ = v___x_1971_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2004_; 
lean_dec_ref(v_env_1948_);
lean_dec(v_declHint_1943_);
v___x_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2004_, 0, v_msg_1942_);
return v___x_2004_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_2005_, lean_object* v_declHint_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_2005_, v_declHint_2006_, v___y_2007_);
lean_dec(v___y_2007_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_2010_, lean_object* v_declHint_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v___x_2017_; lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2027_; 
v___x_2017_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_2010_, v_declHint_2011_, v___y_2015_);
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2020_ = v___x_2017_;
v_isShared_2021_ = v_isSharedCheck_2027_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2017_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2027_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2025_; 
v___x_2022_ = l_Lean_unknownIdentifierMessageTag;
v___x_2023_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
lean_ctor_set(v___x_2023_, 1, v_a_2018_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v___x_2023_);
v___x_2025_ = v___x_2020_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_2028_, lean_object* v_declHint_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2028_, v_declHint_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object* v_msgData_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v___x_2042_; lean_object* v_env_2043_; lean_object* v___x_2044_; lean_object* v_toCold_2045_; lean_object* v_mctx_2046_; lean_object* v_lctx_2047_; lean_object* v_options_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2042_ = lean_st_ref_get(v___y_2040_);
v_env_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc_ref(v_env_2043_);
lean_dec(v___x_2042_);
v___x_2044_ = lean_st_ref_get(v___y_2038_);
v_toCold_2045_ = lean_ctor_get(v___y_2039_, 0);
v_mctx_2046_ = lean_ctor_get(v___x_2044_, 0);
lean_inc_ref(v_mctx_2046_);
lean_dec(v___x_2044_);
v_lctx_2047_ = lean_ctor_get(v___y_2037_, 2);
v_options_2048_ = lean_ctor_get(v_toCold_2045_, 2);
lean_inc_ref(v_options_2048_);
lean_inc_ref(v_lctx_2047_);
v___x_2049_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2049_, 0, v_env_2043_);
lean_ctor_set(v___x_2049_, 1, v_mctx_2046_);
lean_ctor_set(v___x_2049_, 2, v_lctx_2047_);
lean_ctor_set(v___x_2049_, 3, v_options_2048_);
v___x_2050_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
lean_ctor_set(v___x_2050_, 1, v_msgData_2036_);
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v_ref_2065_; lean_object* v___x_2066_; lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2075_; 
v_ref_2065_ = lean_ctor_get(v___y_2062_, 2);
v___x_2066_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v___x_2073_; 
lean_inc(v_ref_2065_);
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v_ref_2065_);
lean_ctor_set(v___x_2071_, 1, v_a_2067_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set_tag(v___x_2069_, 1);
lean_ctor_set(v___x_2069_, 0, v___x_2071_);
v___x_2073_ = v___x_2069_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_2083_, lean_object* v_msg_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v_toCold_2090_; lean_object* v_currRecDepth_2091_; lean_object* v_ref_2092_; uint16_t v_optionFlags_2093_; uint8_t v_suppressElabErrors_2094_; uint8_t v_isRecordingDeps_2095_; lean_object* v_ref_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v_toCold_2090_ = lean_ctor_get(v___y_2087_, 0);
v_currRecDepth_2091_ = lean_ctor_get(v___y_2087_, 1);
v_ref_2092_ = lean_ctor_get(v___y_2087_, 2);
v_optionFlags_2093_ = lean_ctor_get_uint16(v___y_2087_, sizeof(void*)*3);
v_suppressElabErrors_2094_ = lean_ctor_get_uint8(v___y_2087_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2095_ = lean_ctor_get_uint8(v___y_2087_, sizeof(void*)*3 + 3);
v_ref_2096_ = l_Lean_replaceRef(v_ref_2083_, v_ref_2092_);
lean_inc(v_currRecDepth_2091_);
lean_inc_ref(v_toCold_2090_);
v___x_2097_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2097_, 0, v_toCold_2090_);
lean_ctor_set(v___x_2097_, 1, v_currRecDepth_2091_);
lean_ctor_set(v___x_2097_, 2, v_ref_2096_);
lean_ctor_set_uint16(v___x_2097_, sizeof(void*)*3, v_optionFlags_2093_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*3 + 2, v_suppressElabErrors_2094_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*3 + 3, v_isRecordingDeps_2095_);
v___x_2098_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_2084_, v___y_2085_, v___y_2086_, v___x_2097_, v___y_2088_);
lean_dec_ref_known(v___x_2097_, 3);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_2099_, lean_object* v_msg_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_2099_, v_msg_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v_ref_2099_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_2107_, lean_object* v_msg_2108_, lean_object* v_declHint_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; lean_object* v_a_2116_; lean_object* v___x_2117_; 
v___x_2115_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2108_, v_declHint_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref(v___x_2115_);
v___x_2117_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_2107_, v_a_2116_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_2118_, lean_object* v_msg_2119_, lean_object* v_declHint_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_2118_, v_msg_2119_, v_declHint_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v_ref_2118_);
return v_res_2126_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2128_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_2129_ = l_Lean_stringToMessageData(v___x_2128_);
return v___x_2129_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2));
v___x_2132_ = l_Lean_stringToMessageData(v___x_2131_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_2133_, lean_object* v_constName_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v___x_2140_; uint8_t v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2140_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_2141_ = 0;
lean_inc(v_constName_2134_);
v___x_2142_ = l_Lean_MessageData_ofConstName(v_constName_2134_, v___x_2141_);
v___x_2143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2140_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_2145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_2133_, v___x_2145_, v_constName_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_2147_, lean_object* v_constName_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2147_, v_constName_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v_ref_2147_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v_ref_2161_; lean_object* v___x_2162_; 
v_ref_2161_ = lean_ctor_get(v___y_2158_, 2);
v___x_2162_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2161_, v_constName_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(lean_object* v_constName_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___x_2176_; lean_object* v_env_2177_; uint8_t v___x_2178_; lean_object* v___x_2179_; 
v___x_2176_ = lean_st_ref_get(v___y_2174_);
v_env_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc_ref(v_env_2177_);
lean_dec(v___x_2176_);
v___x_2178_ = 0;
lean_inc(v_constName_2170_);
v___x_2179_ = l_Lean_Environment_find_x3f(v_env_2177_, v_constName_2170_, v___x_2178_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
return v___x_2180_;
}
else
{
lean_object* v_val_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec(v_constName_2170_);
v_val_2181_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2179_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_val_2181_);
lean_dec(v___x_2179_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
lean_ctor_set_tag(v___x_2183_, 0);
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_val_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0___boxed(lean_object* v_constName_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(v_constName_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(lean_object* v_declName_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = lean_box(0);
lean_inc(v_declName_2196_);
v___x_2203_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(v_declName_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2229_; 
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2229_ == 0)
{
lean_object* v_unused_2230_; 
v_unused_2230_ = lean_ctor_get(v___x_2203_, 0);
lean_dec(v_unused_2230_);
v___x_2205_ = v___x_2203_;
v_isShared_2206_ = v_isSharedCheck_2229_;
goto v_resetjp_2204_;
}
else
{
lean_dec(v___x_2203_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2229_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; lean_object* v_env_2208_; lean_object* v___x_2209_; 
v___x_2207_ = lean_st_ref_get(v___y_2200_);
v_env_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc_ref(v_env_2208_);
lean_dec(v___x_2207_);
v___x_2209_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2208_, v_declName_2196_);
lean_dec(v_declName_2196_);
lean_dec_ref(v_env_2208_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2210_ = lean_box(0);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2210_);
v___x_2212_ = v___x_2205_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
else
{
lean_object* v_val_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2228_; 
v_val_2214_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2216_ = v___x_2209_;
v_isShared_2217_ = v_isSharedCheck_2228_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_val_2214_);
lean_dec(v___x_2209_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2228_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2218_; lean_object* v_env_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2223_; 
v___x_2218_ = lean_st_ref_get(v___y_2200_);
v_env_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc_ref(v_env_2219_);
lean_dec(v___x_2218_);
v___x_2220_ = l_Lean_Environment_allImportedModuleNames(v_env_2219_);
lean_dec_ref(v_env_2219_);
v___x_2221_ = lean_array_get(v___x_2202_, v___x_2220_, v_val_2214_);
lean_dec(v_val_2214_);
lean_dec_ref(v___x_2220_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 0, v___x_2221_);
v___x_2223_ = v___x_2216_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2221_);
v___x_2223_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
lean_object* v___x_2225_; 
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2223_);
v___x_2225_ = v___x_2205_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec(v_declName_2196_);
v_a_2231_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2203_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2203_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0___boxed(lean_object* v_declName_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(v_declName_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(lean_object* v_decl_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(v_decl_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2285_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2261_ = v___x_2258_;
v_isShared_2262_ = v_isSharedCheck_2285_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2258_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2285_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
if (lean_obj_tag(v_a_2259_) == 1)
{
lean_object* v_val_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2280_; 
v_val_2263_ = lean_ctor_get(v_a_2259_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v_a_2259_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2265_ = v_a_2259_;
v_isShared_2266_ = v_isSharedCheck_2280_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_val_2263_);
lean_dec(v_a_2259_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2280_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2267_; uint8_t v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2275_; 
v___x_2267_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__1));
v___x_2268_ = 1;
v___x_2269_ = l_Lean_Name_toString(v_val_2263_, v___x_2268_);
v___x_2270_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
v___x_2271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2267_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
v___x_2272_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__3));
v___x_2273_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2271_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 0, v___x_2273_);
v___x_2275_ = v___x_2265_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2273_);
v___x_2275_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
lean_object* v___x_2277_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 0, v___x_2275_);
v___x_2277_ = v___x_2261_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
else
{
lean_object* v___x_2281_; lean_object* v___x_2283_; 
lean_dec(v_a_2259_);
v___x_2281_ = lean_box(0);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 0, v___x_2281_);
v___x_2283_ = v___x_2261_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2281_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
v_a_2286_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2258_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2258_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___boxed(lean_object* v_decl_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(v_decl_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2301_, lean_object* v_constName_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2309_, lean_object* v_constName_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1(v_00_u03b1_2309_, v_constName_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2317_, lean_object* v_ref_2318_, lean_object* v_constName_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2318_, v_constName_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2326_, lean_object* v_ref_2327_, lean_object* v_constName_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2326_, v_ref_2327_, v_constName_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v_ref_2327_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_2335_, lean_object* v_ref_2336_, lean_object* v_msg_2337_, lean_object* v_declHint_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_2336_, v_msg_2337_, v_declHint_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2345_, lean_object* v_ref_2346_, lean_object* v_msg_2347_, lean_object* v_declHint_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_00_u03b1_2345_, v_ref_2346_, v_msg_2347_, v_declHint_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v_ref_2346_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_2355_, lean_object* v_declHint_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_2355_, v_declHint_2356_, v___y_2360_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2363_, lean_object* v_declHint_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_2363_, v_declHint_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_2371_, lean_object* v_ref_2372_, lean_object* v_msg_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_2372_, v_msg_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2380_, lean_object* v_ref_2381_, lean_object* v_msg_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_2380_, v_ref_2381_, v_msg_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v_ref_2381_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_2389_, lean_object* v_msg_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2397_, lean_object* v_msg_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_2397_, v_msg_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
return v_res_2404_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(lean_object* v_a_2405_){
_start:
{
switch(lean_obj_tag(v_a_2405_))
{
case 3:
{
uint8_t v___x_2406_; 
v___x_2406_ = 1;
return v___x_2406_;
}
case 6:
{
lean_object* v_a_2407_; 
v_a_2407_ = lean_ctor_get(v_a_2405_, 0);
v_a_2405_ = v_a_2407_;
goto _start;
}
case 4:
{
lean_object* v_f_2409_; 
v_f_2409_ = lean_ctor_get(v_a_2405_, 1);
v_a_2405_ = v_f_2409_;
goto _start;
}
case 7:
{
lean_object* v_a_2411_; 
v_a_2411_ = lean_ctor_get(v_a_2405_, 1);
v_a_2405_ = v_a_2411_;
goto _start;
}
default: 
{
uint8_t v___x_2413_; 
v___x_2413_ = 0;
return v___x_2413_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat___boxed(lean_object* v_a_2414_){
_start:
{
uint8_t v_res_2415_; lean_object* v_r_2416_; 
v_res_2415_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(v_a_2414_);
lean_dec(v_a_2414_);
v_r_2416_ = lean_box(v_res_2415_);
return v_r_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(lean_object* v_e_2417_, lean_object* v___y_2418_){
_start:
{
uint8_t v___x_2420_; 
v___x_2420_ = l_Lean_Expr_hasMVar(v_e_2417_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; 
v___x_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2421_, 0, v_e_2417_);
return v___x_2421_;
}
else
{
lean_object* v___x_2422_; lean_object* v_mctx_2423_; lean_object* v___x_2424_; lean_object* v_fst_2425_; lean_object* v_snd_2426_; lean_object* v___x_2427_; lean_object* v_cache_2428_; lean_object* v_zetaDeltaFVarIds_2429_; lean_object* v_postponed_2430_; lean_object* v_diag_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2440_; 
v___x_2422_ = lean_st_ref_get(v___y_2418_);
v_mctx_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc_ref(v_mctx_2423_);
lean_dec(v___x_2422_);
v___x_2424_ = l_Lean_instantiateMVarsCore(v_mctx_2423_, v_e_2417_);
v_fst_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_fst_2425_);
v_snd_2426_ = lean_ctor_get(v___x_2424_, 1);
lean_inc(v_snd_2426_);
lean_dec_ref(v___x_2424_);
v___x_2427_ = lean_st_ref_take(v___y_2418_);
v_cache_2428_ = lean_ctor_get(v___x_2427_, 1);
v_zetaDeltaFVarIds_2429_ = lean_ctor_get(v___x_2427_, 2);
v_postponed_2430_ = lean_ctor_get(v___x_2427_, 3);
v_diag_2431_ = lean_ctor_get(v___x_2427_, 4);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2440_ == 0)
{
lean_object* v_unused_2441_; 
v_unused_2441_ = lean_ctor_get(v___x_2427_, 0);
lean_dec(v_unused_2441_);
v___x_2433_ = v___x_2427_;
v_isShared_2434_ = v_isSharedCheck_2440_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_diag_2431_);
lean_inc(v_postponed_2430_);
lean_inc(v_zetaDeltaFVarIds_2429_);
lean_inc(v_cache_2428_);
lean_dec(v___x_2427_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2440_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 0, v_snd_2426_);
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_snd_2426_);
lean_ctor_set(v_reuseFailAlloc_2439_, 1, v_cache_2428_);
lean_ctor_set(v_reuseFailAlloc_2439_, 2, v_zetaDeltaFVarIds_2429_);
lean_ctor_set(v_reuseFailAlloc_2439_, 3, v_postponed_2430_);
lean_ctor_set(v_reuseFailAlloc_2439_, 4, v_diag_2431_);
v___x_2436_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = lean_st_ref_put(v___y_2418_, v___x_2436_);
v___x_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2438_, 0, v_fst_2425_);
return v___x_2438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg___boxed(lean_object* v_e_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_e_2442_, v___y_2443_);
lean_dec(v___y_2443_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0(lean_object* v_e_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v___x_2452_; 
v___x_2452_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_e_2446_, v___y_2448_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___boxed(lean_object* v_e_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0(v_e_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(lean_object* v_i_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
switch(lean_obj_tag(v_i_2471_))
{
case 1:
{
lean_object* v_i_2477_; lean_object* v_expr_2478_; uint8_t v_isDisplayableTerm_2479_; lean_object* v___x_2480_; lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2601_; 
v_i_2477_ = lean_ctor_get(v_i_2471_, 0);
lean_inc_ref(v_i_2477_);
lean_dec_ref_known(v_i_2471_, 1);
v_expr_2478_ = lean_ctor_get(v_i_2477_, 3);
lean_inc_ref(v_expr_2478_);
v_isDisplayableTerm_2479_ = lean_ctor_get_uint8(v_i_2477_, sizeof(void*)*4 + 1);
lean_dec_ref(v_i_2477_);
v___x_2480_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_expr_2478_, v_a_2473_);
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2483_ = v___x_2480_;
v_isShared_2484_ = v_isSharedCheck_2601_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2480_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2601_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
uint8_t v___x_2485_; 
v___x_2485_ = l_Lean_Expr_isSort(v_a_2481_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; 
lean_del_object(v___x_2483_);
lean_inc(v_a_2475_);
lean_inc_ref(v_a_2474_);
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
lean_inc(v_a_2481_);
v___x_2486_ = lean_infer_type(v_a_2481_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; lean_object* v___x_2488_; lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2588_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2487_);
lean_dec_ref_known(v___x_2486_, 1);
v___x_2488_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_a_2487_, v_a_2473_);
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2491_ = v___x_2488_;
v_isShared_2492_ = v_isSharedCheck_2588_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2488_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2588_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Lean_Meta_ppExpr(v_a_2489_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2493_) == 0)
{
if (lean_obj_tag(v_a_2481_) == 4)
{
lean_object* v_declName_2494_; lean_object* v___x_2495_; 
lean_dec_ref_known(v___x_2493_, 1);
v_declName_2494_ = lean_ctor_get(v_a_2481_, 0);
lean_inc_n(v_declName_2494_, 2);
lean_dec_ref_known(v_a_2481_, 2);
v___x_2495_ = l_Lean_PrettyPrinter_ppSignature(v_declName_2494_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; lean_object* v___x_2497_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2496_);
lean_dec_ref_known(v___x_2495_, 1);
v___x_2497_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(v_declName_2494_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2522_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2500_ = v___x_2497_;
v_isShared_2501_ = v_isSharedCheck_2522_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2497_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2522_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v_fmt_2502_; lean_object* v_infos_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2521_; 
v_fmt_2502_ = lean_ctor_get(v_a_2496_, 0);
v_infos_2503_ = lean_ctor_get(v_a_2496_, 1);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_a_2496_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2505_ = v_a_2496_;
v_isShared_2506_ = v_isSharedCheck_2521_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_infos_2503_);
lean_inc(v_fmt_2502_);
lean_dec(v_a_2496_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2521_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2512_; 
v___x_2507_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1));
v___x_2508_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
lean_ctor_set(v___x_2508_, 1, v_fmt_2502_);
v___x_2509_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3));
v___x_2510_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2508_);
lean_ctor_set(v___x_2510_, 1, v___x_2509_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 0, v___x_2510_);
v___x_2512_ = v___x_2505_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2510_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v_infos_2503_);
v___x_2512_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
lean_object* v___x_2514_; 
if (v_isShared_2492_ == 0)
{
lean_ctor_set_tag(v___x_2491_, 1);
lean_ctor_set(v___x_2491_, 0, v___x_2512_);
v___x_2514_ = v___x_2491_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2512_);
v___x_2514_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2515_; lean_object* v___x_2517_; 
v___x_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
lean_ctor_set(v___x_2515_, 1, v_a_2498_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v___x_2515_);
v___x_2517_ = v___x_2500_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
}
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_dec(v_a_2496_);
lean_del_object(v___x_2491_);
v_a_2523_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2497_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2497_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec(v_declName_2494_);
lean_del_object(v___x_2491_);
v_a_2531_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2495_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2495_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2540_; 
v_a_2539_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2539_);
lean_dec_ref_known(v___x_2493_, 1);
lean_inc(v_a_2481_);
v___x_2540_ = l_Lean_Meta_ppExpr(v_a_2481_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2571_; 
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2543_ = v___x_2540_;
v_isShared_2544_ = v_isSharedCheck_2571_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2540_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2571_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___y_2546_; 
if (v_isDisplayableTerm_2479_ == 0)
{
if (lean_obj_tag(v_a_2481_) == 1)
{
lean_object* v_lctx_2565_; lean_object* v___x_2566_; 
v_lctx_2565_ = lean_ctor_get(v_a_2472_, 2);
lean_inc_ref(v_lctx_2565_);
v___x_2566_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_2565_, v_a_2481_);
lean_dec_ref_known(v_a_2481_, 1);
if (lean_obj_tag(v___x_2566_) == 1)
{
lean_object* v_val_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v_val_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_val_2567_);
lean_dec_ref_known(v___x_2566_, 1);
v___x_2568_ = l_Lean_LocalDecl_userName(v_val_2567_);
lean_dec(v_val_2567_);
v___x_2569_ = l_Lean_Name_hasMacroScopes(v___x_2568_);
lean_dec(v___x_2568_);
if (v___x_2569_ == 0)
{
goto v___jp_2561_;
}
else
{
lean_dec(v_a_2541_);
v___y_2546_ = v_a_2539_;
goto v___jp_2545_;
}
}
else
{
lean_dec(v___x_2566_);
lean_dec(v_a_2541_);
v___y_2546_ = v_a_2539_;
goto v___jp_2545_;
}
}
else
{
uint8_t v___x_2570_; 
lean_dec(v_a_2481_);
v___x_2570_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(v_a_2541_);
if (v___x_2570_ == 0)
{
lean_dec(v_a_2541_);
v___y_2546_ = v_a_2539_;
goto v___jp_2545_;
}
else
{
goto v___jp_2561_;
}
}
}
else
{
lean_dec(v_a_2481_);
goto v___jp_2561_;
}
v___jp_2545_:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2554_; 
v___x_2547_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1));
v___x_2548_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
lean_ctor_set(v___x_2548_, 1, v___y_2546_);
v___x_2549_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3));
v___x_2550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
v___x_2551_ = lean_box(1);
v___x_2552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2550_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set_tag(v___x_2491_, 1);
lean_ctor_set(v___x_2491_, 0, v___x_2552_);
v___x_2554_ = v___x_2491_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2552_);
v___x_2554_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2558_; 
v___x_2555_ = lean_box(0);
v___x_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2554_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v___x_2556_);
v___x_2558_ = v___x_2543_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2556_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
v___jp_2561_:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2562_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5));
v___x_2563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2563_, 0, v_a_2541_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
lean_ctor_set(v___x_2564_, 1, v_a_2539_);
v___y_2546_ = v___x_2564_;
goto v___jp_2545_;
}
}
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_dec(v_a_2539_);
lean_del_object(v___x_2491_);
lean_dec(v_a_2481_);
v_a_2572_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2540_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2540_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
lean_del_object(v___x_2491_);
lean_dec(v_a_2481_);
v_a_2580_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2493_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2493_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec(v_a_2481_);
v_a_2589_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2486_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2486_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
else
{
lean_object* v___x_2597_; lean_object* v___x_2599_; 
lean_dec(v_a_2481_);
v___x_2597_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6));
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 0, v___x_2597_);
v___x_2599_ = v___x_2483_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
case 7:
{
lean_object* v_i_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2652_; 
v_i_2602_ = lean_ctor_get(v_i_2471_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_i_2471_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2604_ = v_i_2471_;
v_isShared_2605_ = v_isSharedCheck_2652_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_i_2602_);
lean_dec(v_i_2471_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2652_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v_fieldName_2606_; lean_object* v_val_2607_; lean_object* v___x_2608_; 
v_fieldName_2606_ = lean_ctor_get(v_i_2602_, 1);
lean_inc(v_fieldName_2606_);
v_val_2607_ = lean_ctor_get(v_i_2602_, 3);
lean_inc_ref(v_val_2607_);
lean_dec_ref(v_i_2602_);
lean_inc(v_a_2475_);
lean_inc_ref(v_a_2474_);
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
v___x_2608_ = lean_infer_type(v_val_2607_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2610_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2609_);
lean_dec_ref_known(v___x_2608_, 1);
v___x_2610_ = l_Lean_Meta_ppExpr(v_a_2609_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2635_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2613_ = v___x_2610_;
v_isShared_2614_ = v_isSharedCheck_2635_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2610_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2635_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2615_; uint8_t v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2619_; 
v___x_2615_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1));
v___x_2616_ = 1;
v___x_2617_ = l_Lean_Name_toString(v_fieldName_2606_, v___x_2616_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set_tag(v___x_2604_, 3);
lean_ctor_set(v___x_2604_, 0, v___x_2617_);
v___x_2619_ = v___x_2604_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2617_);
v___x_2619_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2632_; 
v___x_2620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2615_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
v___x_2621_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5));
v___x_2622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2620_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
v___x_2623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
lean_ctor_set(v___x_2623_, 1, v_a_2611_);
v___x_2624_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3));
v___x_2625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2623_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
v___x_2626_ = lean_box(1);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2625_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2627_);
v___x_2629_ = lean_box(0);
v___x_2630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2628_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 0, v___x_2630_);
v___x_2632_ = v___x_2613_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v___x_2630_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
else
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
lean_dec(v_fieldName_2606_);
lean_del_object(v___x_2604_);
v_a_2636_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2610_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2610_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v_fieldName_2606_);
lean_del_object(v___x_2604_);
v_a_2644_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2608_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2608_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
default: 
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_dec_ref(v_i_2471_);
v___x_2653_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6));
v___x_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
return v___x_2654_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___boxed(lean_object* v_i_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(v_i_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__0(lean_object* v_snd_2662_, lean_object* v_____r_2663_, lean_object* v_fmts_2664_, lean_object* v_infos_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2671_, 0, v_fmts_2664_);
lean_ctor_set(v___x_2671_, 1, v_infos_2665_);
v___x_2672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2672_, 0, v_snd_2662_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
v___x_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2672_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__0___boxed(lean_object* v_snd_2674_, lean_object* v_____r_2675_, lean_object* v_fmts_2676_, lean_object* v_infos_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(v_snd_2674_, v_____r_2675_, v_fmts_2676_, v_infos_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0_spec__0(lean_object* v_x_2684_, lean_object* v_x_2685_, lean_object* v_x_2686_){
_start:
{
if (lean_obj_tag(v_x_2686_) == 0)
{
lean_dec(v_x_2684_);
return v_x_2685_;
}
else
{
lean_object* v_head_2687_; lean_object* v_tail_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2697_; 
v_head_2687_ = lean_ctor_get(v_x_2686_, 0);
v_tail_2688_ = lean_ctor_get(v_x_2686_, 1);
v_isSharedCheck_2697_ = !lean_is_exclusive(v_x_2686_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2690_ = v_x_2686_;
v_isShared_2691_ = v_isSharedCheck_2697_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_tail_2688_);
lean_inc(v_head_2687_);
lean_dec(v_x_2686_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2697_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
lean_inc(v_x_2684_);
if (v_isShared_2691_ == 0)
{
lean_ctor_set_tag(v___x_2690_, 5);
lean_ctor_set(v___x_2690_, 1, v_x_2684_);
lean_ctor_set(v___x_2690_, 0, v_x_2685_);
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_x_2685_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v_x_2684_);
v___x_2693_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2694_; 
v___x_2694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
lean_ctor_set(v___x_2694_, 1, v_head_2687_);
v_x_2685_ = v___x_2694_;
v_x_2686_ = v_tail_2688_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0(lean_object* v_x_2698_, lean_object* v_x_2699_){
_start:
{
if (lean_obj_tag(v_x_2698_) == 0)
{
lean_object* v___x_2700_; 
lean_dec(v_x_2699_);
v___x_2700_ = lean_box(0);
return v___x_2700_;
}
else
{
lean_object* v_tail_2701_; 
v_tail_2701_ = lean_ctor_get(v_x_2698_, 1);
if (lean_obj_tag(v_tail_2701_) == 0)
{
lean_object* v_head_2702_; 
lean_dec(v_x_2699_);
v_head_2702_ = lean_ctor_get(v_x_2698_, 0);
lean_inc(v_head_2702_);
lean_dec_ref_known(v_x_2698_, 2);
return v_head_2702_;
}
else
{
lean_object* v_head_2703_; lean_object* v___x_2704_; 
lean_inc(v_tail_2701_);
v_head_2703_ = lean_ctor_get(v_x_2698_, 0);
lean_inc(v_head_2703_);
lean_dec_ref_known(v_x_2698_, 2);
v___x_2704_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0_spec__0(v_x_2699_, v_head_2703_, v_tail_2701_);
return v___x_2704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__1(lean_object* v___x_2708_, lean_object* v_i_2709_, lean_object* v_fmts_2710_, lean_object* v_infos_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v___y_2718_; lean_object* v_fmts_2719_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v_fmts_2733_; lean_object* v_fst_2737_; lean_object* v_fst_2738_; lean_object* v_snd_2739_; lean_object* v___y_2760_; uint8_t v___y_2761_; lean_object* v_a_2765_; lean_object* v___y_2769_; lean_object* v___x_2775_; 
lean_inc_ref(v_i_2709_);
v___x_2775_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(v_i_2709_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v_fst_2777_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2776_);
lean_dec_ref_known(v___x_2775_, 1);
v_fst_2777_ = lean_ctor_get(v_a_2776_, 0);
if (lean_obj_tag(v_fst_2777_) == 1)
{
lean_object* v_val_2778_; lean_object* v_snd_2779_; lean_object* v_fmt_2780_; lean_object* v_infos_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
lean_dec(v_infos_2711_);
v_val_2778_ = lean_ctor_get(v_fst_2777_, 0);
lean_inc(v_val_2778_);
v_snd_2779_ = lean_ctor_get(v_a_2776_, 1);
lean_inc(v_snd_2779_);
lean_dec(v_a_2776_);
v_fmt_2780_ = lean_ctor_get(v_val_2778_, 0);
lean_inc(v_fmt_2780_);
v_infos_2781_ = lean_ctor_get(v_val_2778_, 1);
lean_inc(v_infos_2781_);
lean_dec(v_val_2778_);
v___x_2782_ = lean_array_push(v_fmts_2710_, v_fmt_2780_);
v___x_2783_ = lean_box(0);
v___x_2784_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(v_snd_2779_, v___x_2783_, v___x_2782_, v_infos_2781_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
v___y_2769_ = v___x_2784_;
goto v___jp_2768_;
}
else
{
lean_object* v_snd_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v_snd_2785_ = lean_ctor_get(v_a_2776_, 1);
lean_inc(v_snd_2785_);
lean_dec(v_a_2776_);
v___x_2786_ = lean_box(0);
v___x_2787_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(v_snd_2785_, v___x_2786_, v_fmts_2710_, v_infos_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
v___y_2769_ = v___x_2787_;
goto v___jp_2768_;
}
}
else
{
lean_object* v_a_2788_; 
v_a_2788_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2788_);
lean_dec_ref_known(v___x_2775_, 1);
v_a_2765_ = v_a_2788_;
goto v___jp_2764_;
}
v___jp_2717_:
{
lean_object* v___x_2720_; uint8_t v___x_2721_; 
v___x_2720_ = lean_array_get_size(v_fmts_2719_);
v___x_2721_ = lean_nat_dec_eq(v___x_2720_, v___x_2708_);
if (v___x_2721_ == 0)
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2722_ = lean_array_to_list(v_fmts_2719_);
v___x_2723_ = ((lean_object*)(l_Lean_Elab_Info_fmtHover_x3f___lam__1___closed__1));
v___x_2724_ = l_Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0(v___x_2722_, v___x_2723_);
v___x_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
lean_ctor_set(v___x_2725_, 1, v___y_2718_);
v___x_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2725_);
v___x_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
return v___x_2727_;
}
else
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
lean_dec_ref(v_fmts_2719_);
lean_dec(v___y_2718_);
v___x_2728_ = lean_box(0);
v___x_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
return v___x_2729_;
}
}
v___jp_2730_:
{
if (lean_obj_tag(v___y_2731_) == 1)
{
lean_object* v_val_2734_; lean_object* v___x_2735_; 
v_val_2734_ = lean_ctor_get(v___y_2731_, 0);
lean_inc(v_val_2734_);
lean_dec_ref_known(v___y_2731_, 1);
v___x_2735_ = lean_array_push(v_fmts_2733_, v_val_2734_);
v___y_2718_ = v___y_2732_;
v_fmts_2719_ = v___x_2735_;
goto v___jp_2717_;
}
else
{
lean_dec(v___y_2731_);
v___y_2718_ = v___y_2732_;
v_fmts_2719_ = v_fmts_2733_;
goto v___jp_2717_;
}
}
v___jp_2736_:
{
lean_object* v___x_2740_; 
v___x_2740_ = l_Lean_Elab_Info_docString_x3f(v_i_2709_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref_known(v___x_2740_, 1);
if (lean_obj_tag(v_a_2741_) == 1)
{
lean_object* v_val_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2750_; 
v_val_2742_ = lean_ctor_get(v_a_2741_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v_a_2741_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2744_ = v_a_2741_;
v_isShared_2745_ = v_isSharedCheck_2750_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_val_2742_);
lean_dec(v_a_2741_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2750_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
lean_ctor_set_tag(v___x_2744_, 3);
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_val_2742_);
v___x_2747_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
lean_object* v___x_2748_; 
v___x_2748_ = lean_array_push(v_fst_2738_, v___x_2747_);
v___y_2731_ = v_fst_2737_;
v___y_2732_ = v_snd_2739_;
v_fmts_2733_ = v___x_2748_;
goto v___jp_2730_;
}
}
}
else
{
lean_dec(v_a_2741_);
v___y_2731_ = v_fst_2737_;
v___y_2732_ = v_snd_2739_;
v_fmts_2733_ = v_fst_2738_;
goto v___jp_2730_;
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec(v_snd_2739_);
lean_dec(v_fst_2738_);
lean_dec(v_fst_2737_);
v_a_2751_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2740_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2740_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
v___jp_2759_:
{
if (v___y_2761_ == 0)
{
lean_object* v___x_2762_; 
lean_dec_ref(v___y_2760_);
v___x_2762_ = lean_box(0);
v_fst_2737_ = v___x_2762_;
v_fst_2738_ = v_fmts_2710_;
v_snd_2739_ = v_infos_2711_;
goto v___jp_2736_;
}
else
{
lean_object* v___x_2763_; 
lean_dec(v_infos_2711_);
lean_dec_ref(v_fmts_2710_);
lean_dec_ref(v_i_2709_);
v___x_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2763_, 0, v___y_2760_);
return v___x_2763_;
}
}
v___jp_2764_:
{
uint8_t v___x_2766_; 
v___x_2766_ = l_Lean_Exception_isInterrupt(v_a_2765_);
if (v___x_2766_ == 0)
{
uint8_t v___x_2767_; 
lean_inc_ref(v_a_2765_);
v___x_2767_ = l_Lean_Exception_isRuntime(v_a_2765_);
v___y_2760_ = v_a_2765_;
v___y_2761_ = v___x_2767_;
goto v___jp_2759_;
}
else
{
v___y_2760_ = v_a_2765_;
v___y_2761_ = v___x_2766_;
goto v___jp_2759_;
}
}
v___jp_2768_:
{
lean_object* v_a_2770_; lean_object* v_snd_2771_; lean_object* v_fst_2772_; lean_object* v_fst_2773_; lean_object* v_snd_2774_; 
v_a_2770_ = lean_ctor_get(v___y_2769_, 0);
lean_inc(v_a_2770_);
lean_dec_ref(v___y_2769_);
v_snd_2771_ = lean_ctor_get(v_a_2770_, 1);
lean_inc(v_snd_2771_);
v_fst_2772_ = lean_ctor_get(v_a_2770_, 0);
lean_inc(v_fst_2772_);
lean_dec(v_a_2770_);
v_fst_2773_ = lean_ctor_get(v_snd_2771_, 0);
lean_inc(v_fst_2773_);
v_snd_2774_ = lean_ctor_get(v_snd_2771_, 1);
lean_inc(v_snd_2774_);
lean_dec(v_snd_2771_);
v_fst_2737_ = v_fst_2772_;
v_fst_2738_ = v_fst_2773_;
v_snd_2739_ = v_snd_2774_;
goto v___jp_2736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__1___boxed(lean_object* v___x_2789_, lean_object* v_i_2790_, lean_object* v_fmts_2791_, lean_object* v_infos_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Lean_Elab_Info_fmtHover_x3f___lam__1(v___x_2789_, v_i_2790_, v_fmts_2791_, v_infos_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___x_2789_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f(lean_object* v_ci_2801_, lean_object* v_i_2802_){
_start:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v_fmts_2806_; lean_object* v_infos_2807_; lean_object* v___f_2808_; lean_object* v___x_2809_; 
v___x_2804_ = l_Lean_Elab_Info_lctx(v_i_2802_);
v___x_2805_ = lean_unsigned_to_nat(0u);
v_fmts_2806_ = ((lean_object*)(l_Lean_Elab_Info_fmtHover_x3f___closed__0));
v_infos_2807_ = lean_box(1);
v___f_2808_ = lean_alloc_closure((void*)(l_Lean_Elab_Info_fmtHover_x3f___lam__1___boxed), 9, 4);
lean_closure_set(v___f_2808_, 0, v___x_2805_);
lean_closure_set(v___f_2808_, 1, v_i_2802_);
lean_closure_set(v___f_2808_, 2, v_fmts_2806_);
lean_closure_set(v___f_2808_, 3, v_infos_2807_);
v___x_2809_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ci_2801_, v___x_2804_, v___f_2808_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___boxed(lean_object* v_ci_2810_, lean_object* v_i_2811_, lean_object* v_a_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_Lean_Elab_Info_fmtHover_x3f(v_ci_2810_, v_i_2811_);
return v_res_2813_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(lean_object* v_hoverPos_2822_, lean_object* v_pos_2823_, lean_object* v_tailPos_2824_, lean_object* v_as_2825_, size_t v_i_2826_, size_t v_stop_2827_){
_start:
{
uint8_t v___x_2828_; 
v___x_2828_ = lean_usize_dec_eq(v_i_2826_, v_stop_2827_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; uint8_t v___x_2830_; 
v___x_2829_ = lean_array_uget_borrowed(v_as_2825_, v_i_2826_);
v___x_2830_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(v_hoverPos_2822_, v_pos_2823_, v_tailPos_2824_, v___x_2829_);
if (v___x_2830_ == 0)
{
size_t v___x_2831_; size_t v___x_2832_; 
v___x_2831_ = ((size_t)1ULL);
v___x_2832_ = lean_usize_add(v_i_2826_, v___x_2831_);
v_i_2826_ = v___x_2832_;
goto _start;
}
else
{
return v___x_2830_;
}
}
else
{
uint8_t v___x_2834_; 
v___x_2834_ = 0;
return v___x_2834_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(lean_object* v_hoverPos_2835_, lean_object* v_pos_2836_, lean_object* v_tailPos_2837_, lean_object* v_x_2838_){
_start:
{
if (lean_obj_tag(v_x_2838_) == 0)
{
lean_object* v_cs_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; uint8_t v___x_2842_; 
v_cs_2839_ = lean_ctor_get(v_x_2838_, 0);
v___x_2840_ = lean_unsigned_to_nat(0u);
v___x_2841_ = lean_array_get_size(v_cs_2839_);
v___x_2842_ = lean_nat_dec_lt(v___x_2840_, v___x_2841_);
if (v___x_2842_ == 0)
{
return v___x_2842_;
}
else
{
if (v___x_2842_ == 0)
{
return v___x_2842_;
}
else
{
size_t v___x_2843_; size_t v___x_2844_; uint8_t v___x_2845_; 
v___x_2843_ = ((size_t)0ULL);
v___x_2844_ = lean_usize_of_nat(v___x_2841_);
v___x_2845_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(v_hoverPos_2835_, v_pos_2836_, v_tailPos_2837_, v_cs_2839_, v___x_2843_, v___x_2844_);
return v___x_2845_;
}
}
}
else
{
lean_object* v_vs_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; 
v_vs_2846_ = lean_ctor_get(v_x_2838_, 0);
v___x_2847_ = lean_unsigned_to_nat(0u);
v___x_2848_ = lean_array_get_size(v_vs_2846_);
v___x_2849_ = lean_nat_dec_lt(v___x_2847_, v___x_2848_);
if (v___x_2849_ == 0)
{
return v___x_2849_;
}
else
{
if (v___x_2849_ == 0)
{
return v___x_2849_;
}
else
{
size_t v___x_2850_; size_t v___x_2851_; uint8_t v___x_2852_; 
v___x_2850_ = ((size_t)0ULL);
v___x_2851_ = lean_usize_of_nat(v___x_2848_);
v___x_2852_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_2835_, v_pos_2836_, v_tailPos_2837_, v_vs_2846_, v___x_2850_, v___x_2851_);
return v___x_2852_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(lean_object* v_hoverPos_2853_, lean_object* v_pos_2854_, lean_object* v_tailPos_2855_, lean_object* v_t_2856_){
_start:
{
lean_object* v_root_2857_; lean_object* v_tail_2858_; uint8_t v___x_2859_; 
v_root_2857_ = lean_ctor_get(v_t_2856_, 0);
v_tail_2858_ = lean_ctor_get(v_t_2856_, 1);
v___x_2859_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(v_hoverPos_2853_, v_pos_2854_, v_tailPos_2855_, v_root_2857_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; lean_object* v___x_2861_; uint8_t v___x_2862_; 
v___x_2860_ = lean_unsigned_to_nat(0u);
v___x_2861_ = lean_array_get_size(v_tail_2858_);
v___x_2862_ = lean_nat_dec_lt(v___x_2860_, v___x_2861_);
if (v___x_2862_ == 0)
{
return v___x_2862_;
}
else
{
if (v___x_2862_ == 0)
{
return v___x_2862_;
}
else
{
size_t v___x_2863_; size_t v___x_2864_; uint8_t v___x_2865_; 
v___x_2863_ = ((size_t)0ULL);
v___x_2864_ = lean_usize_of_nat(v___x_2861_);
v___x_2865_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_2853_, v_pos_2854_, v_tailPos_2855_, v_tail_2858_, v___x_2863_, v___x_2864_);
return v___x_2865_;
}
}
}
else
{
return v___x_2859_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(lean_object* v_hoverPos_2866_, lean_object* v_pos_2867_, lean_object* v_tailPos_2868_, lean_object* v_a_2869_){
_start:
{
if (lean_obj_tag(v_a_2869_) == 1)
{
lean_object* v_i_2870_; 
v_i_2870_ = lean_ctor_get(v_a_2869_, 0);
switch(lean_obj_tag(v_i_2870_))
{
case 0:
{
lean_object* v_children_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; uint8_t v___x_2874_; 
v_children_2871_ = lean_ctor_get(v_a_2869_, 1);
v___x_2872_ = l_Lean_Elab_Info_stx(v_i_2870_);
v___x_2873_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3));
v___x_2874_ = l_Lean_Syntax_isOfKind(v___x_2872_, v___x_2873_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_Elab_Info_pos_x3f(v_i_2870_);
if (lean_obj_tag(v___x_2875_) == 1)
{
lean_object* v_val_2876_; lean_object* v___x_2877_; 
v_val_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_val_2876_);
lean_dec_ref_known(v___x_2875_, 1);
v___x_2877_ = l_Lean_Elab_Info_tailPos_x3f(v_i_2870_);
if (lean_obj_tag(v___x_2877_) == 1)
{
lean_object* v_val_2878_; uint8_t v___x_2879_; uint8_t v___y_2881_; lean_object* v___x_2883_; lean_object* v___x_2884_; uint8_t v___x_2885_; 
v_val_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_val_2878_);
lean_dec_ref_known(v___x_2877_, 1);
v___x_2879_ = 1;
v___x_2883_ = lean_unsigned_to_nat(1u);
v___x_2884_ = lean_nat_add(v_hoverPos_2866_, v___x_2883_);
v___x_2885_ = lean_nat_dec_le(v___x_2884_, v_val_2878_);
lean_dec(v___x_2884_);
if (v___x_2885_ == 0)
{
lean_dec(v_val_2878_);
lean_dec(v_val_2876_);
v___y_2881_ = v___x_2874_;
goto v___jp_2880_;
}
else
{
uint8_t v_decide_2886_; 
v_decide_2886_ = lean_nat_dec_eq(v_val_2876_, v_pos_2867_);
lean_dec(v_val_2876_);
if (v_decide_2886_ == 0)
{
lean_dec(v_val_2878_);
v___y_2881_ = v___x_2885_;
goto v___jp_2880_;
}
else
{
uint8_t v_decide_2887_; 
v_decide_2887_ = lean_nat_dec_eq(v_val_2878_, v_tailPos_2868_);
lean_dec(v_val_2878_);
if (v_decide_2887_ == 0)
{
v___y_2881_ = v___x_2885_;
goto v___jp_2880_;
}
else
{
v___y_2881_ = v___x_2874_;
goto v___jp_2880_;
}
}
}
v___jp_2880_:
{
if (v___y_2881_ == 0)
{
uint8_t v___x_2882_; 
v___x_2882_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2866_, v_pos_2867_, v_tailPos_2868_, v_children_2871_);
return v___x_2882_;
}
else
{
return v___x_2879_;
}
}
}
else
{
uint8_t v___x_2888_; 
lean_dec(v___x_2877_);
lean_dec(v_val_2876_);
v___x_2888_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2866_, v_pos_2867_, v_tailPos_2868_, v_children_2871_);
return v___x_2888_;
}
}
else
{
uint8_t v___x_2889_; 
lean_dec(v___x_2875_);
v___x_2889_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2866_, v_pos_2867_, v_tailPos_2868_, v_children_2871_);
return v___x_2889_;
}
}
else
{
uint8_t v___x_2890_; 
v___x_2890_ = 0;
return v___x_2890_;
}
}
case 4:
{
lean_object* v_children_2891_; uint8_t v___x_2892_; 
v_children_2891_ = lean_ctor_get(v_a_2869_, 1);
v___x_2892_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2866_, v_pos_2867_, v_tailPos_2868_, v_children_2891_);
return v___x_2892_;
}
default: 
{
uint8_t v___x_2893_; 
v___x_2893_ = 0;
return v___x_2893_;
}
}
}
else
{
uint8_t v___x_2894_; 
v___x_2894_ = 0;
return v___x_2894_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(lean_object* v_hoverPos_2895_, lean_object* v_pos_2896_, lean_object* v_tailPos_2897_, lean_object* v_as_2898_, size_t v_i_2899_, size_t v_stop_2900_){
_start:
{
uint8_t v___x_2901_; 
v___x_2901_ = lean_usize_dec_eq(v_i_2899_, v_stop_2900_);
if (v___x_2901_ == 0)
{
lean_object* v___x_2902_; uint8_t v___x_2903_; 
v___x_2902_ = lean_array_uget_borrowed(v_as_2898_, v_i_2899_);
v___x_2903_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(v_hoverPos_2895_, v_pos_2896_, v_tailPos_2897_, v___x_2902_);
if (v___x_2903_ == 0)
{
size_t v___x_2904_; size_t v___x_2905_; 
v___x_2904_ = ((size_t)1ULL);
v___x_2905_ = lean_usize_add(v_i_2899_, v___x_2904_);
v_i_2899_ = v___x_2905_;
goto _start;
}
else
{
return v___x_2903_;
}
}
else
{
uint8_t v___x_2907_; 
v___x_2907_ = 0;
return v___x_2907_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1___boxed(lean_object* v_hoverPos_2908_, lean_object* v_pos_2909_, lean_object* v_tailPos_2910_, lean_object* v_as_2911_, lean_object* v_i_2912_, lean_object* v_stop_2913_){
_start:
{
size_t v_i_boxed_2914_; size_t v_stop_boxed_2915_; uint8_t v_res_2916_; lean_object* v_r_2917_; 
v_i_boxed_2914_ = lean_unbox_usize(v_i_2912_);
lean_dec(v_i_2912_);
v_stop_boxed_2915_ = lean_unbox_usize(v_stop_2913_);
lean_dec(v_stop_2913_);
v_res_2916_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_2908_, v_pos_2909_, v_tailPos_2910_, v_as_2911_, v_i_boxed_2914_, v_stop_boxed_2915_);
lean_dec_ref(v_as_2911_);
lean_dec(v_tailPos_2910_);
lean_dec(v_pos_2909_);
lean_dec(v_hoverPos_2908_);
v_r_2917_ = lean_box(v_res_2916_);
return v_r_2917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1___boxed(lean_object* v_hoverPos_2918_, lean_object* v_pos_2919_, lean_object* v_tailPos_2920_, lean_object* v_as_2921_, lean_object* v_i_2922_, lean_object* v_stop_2923_){
_start:
{
size_t v_i_boxed_2924_; size_t v_stop_boxed_2925_; uint8_t v_res_2926_; lean_object* v_r_2927_; 
v_i_boxed_2924_ = lean_unbox_usize(v_i_2922_);
lean_dec(v_i_2922_);
v_stop_boxed_2925_ = lean_unbox_usize(v_stop_2923_);
lean_dec(v_stop_2923_);
v_res_2926_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(v_hoverPos_2918_, v_pos_2919_, v_tailPos_2920_, v_as_2921_, v_i_boxed_2924_, v_stop_boxed_2925_);
lean_dec_ref(v_as_2921_);
lean_dec(v_tailPos_2920_);
lean_dec(v_pos_2919_);
lean_dec(v_hoverPos_2918_);
v_r_2927_ = lean_box(v_res_2926_);
return v_r_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0___boxed(lean_object* v_hoverPos_2928_, lean_object* v_pos_2929_, lean_object* v_tailPos_2930_, lean_object* v_t_2931_){
_start:
{
uint8_t v_res_2932_; lean_object* v_r_2933_; 
v_res_2932_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2928_, v_pos_2929_, v_tailPos_2930_, v_t_2931_);
lean_dec_ref(v_t_2931_);
lean_dec(v_tailPos_2930_);
lean_dec(v_pos_2929_);
lean_dec(v_hoverPos_2928_);
v_r_2933_ = lean_box(v_res_2932_);
return v_r_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0___boxed(lean_object* v_hoverPos_2934_, lean_object* v_pos_2935_, lean_object* v_tailPos_2936_, lean_object* v_x_2937_){
_start:
{
uint8_t v_res_2938_; lean_object* v_r_2939_; 
v_res_2938_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(v_hoverPos_2934_, v_pos_2935_, v_tailPos_2936_, v_x_2937_);
lean_dec_ref(v_x_2937_);
lean_dec(v_tailPos_2936_);
lean_dec(v_pos_2935_);
lean_dec(v_hoverPos_2934_);
v_r_2939_ = lean_box(v_res_2938_);
return v_r_2939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___boxed(lean_object* v_hoverPos_2940_, lean_object* v_pos_2941_, lean_object* v_tailPos_2942_, lean_object* v_a_2943_){
_start:
{
uint8_t v_res_2944_; lean_object* v_r_2945_; 
v_res_2944_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(v_hoverPos_2940_, v_pos_2941_, v_tailPos_2942_, v_a_2943_);
lean_dec_ref(v_a_2943_);
lean_dec(v_tailPos_2942_);
lean_dec(v_pos_2941_);
lean_dec(v_hoverPos_2940_);
v_r_2945_ = lean_box(v_res_2944_);
return v_r_2945_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock(lean_object* v_stx_2947_){
_start:
{
lean_object* v___x_2948_; uint8_t v___x_2949_; 
v___x_2948_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock___closed__0));
lean_inc(v_stx_2947_);
v___x_2949_ = l_Lean_Syntax_isToken(v___x_2948_, v_stx_2947_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; lean_object* v___x_2951_; uint8_t v___x_2952_; 
v___x_2950_ = l_Lean_Syntax_getNumArgs(v_stx_2947_);
v___x_2951_ = lean_unsigned_to_nat(2u);
v___x_2952_ = lean_nat_dec_eq(v___x_2950_, v___x_2951_);
lean_dec(v___x_2950_);
if (v___x_2952_ == 0)
{
lean_dec(v_stx_2947_);
return v___x_2952_;
}
else
{
lean_object* v___x_2953_; lean_object* v___x_2954_; uint8_t v___x_2955_; 
v___x_2953_ = lean_unsigned_to_nat(0u);
v___x_2954_ = l_Lean_Syntax_getArg(v_stx_2947_, v___x_2953_);
lean_dec(v_stx_2947_);
v___x_2955_ = l_Lean_Syntax_isToken(v___x_2948_, v___x_2954_);
return v___x_2955_;
}
}
else
{
lean_dec(v_stx_2947_);
return v___x_2949_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock___boxed(lean_object* v_stx_2956_){
_start:
{
uint8_t v_res_2957_; lean_object* v_r_2958_; 
v_res_2957_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock(v_stx_2956_);
v_r_2958_ = lean_box(v_res_2957_);
return v_r_2958_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(lean_object* v_x_2959_, lean_object* v_x_2960_){
_start:
{
if (lean_obj_tag(v_x_2959_) == 0)
{
if (lean_obj_tag(v_x_2960_) == 0)
{
uint8_t v___x_2961_; 
v___x_2961_ = 1;
return v___x_2961_;
}
else
{
uint8_t v___x_2962_; 
v___x_2962_ = 0;
return v___x_2962_;
}
}
else
{
if (lean_obj_tag(v_x_2960_) == 0)
{
uint8_t v___x_2963_; 
v___x_2963_ = 0;
return v___x_2963_;
}
else
{
lean_object* v_val_2964_; lean_object* v_val_2965_; uint8_t v___x_2966_; 
v_val_2964_ = lean_ctor_get(v_x_2959_, 0);
v_val_2965_ = lean_ctor_get(v_x_2960_, 0);
v___x_2966_ = lean_nat_dec_eq(v_val_2964_, v_val_2965_);
return v___x_2966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4___boxed(lean_object* v_x_2967_, lean_object* v_x_2968_){
_start:
{
uint8_t v_res_2969_; lean_object* v_r_2970_; 
v_res_2969_ = l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(v_x_2967_, v_x_2968_);
lean_dec(v_x_2968_);
lean_dec(v_x_2967_);
v_r_2970_ = lean_box(v_res_2969_);
return v_r_2970_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(lean_object* v_hoverCol_2971_, lean_object* v_col_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_){
_start:
{
if (lean_obj_tag(v_a_2973_) == 0)
{
lean_object* v___x_2975_; 
v___x_2975_ = l_List_reverse___redArg(v_a_2974_);
return v___x_2975_;
}
else
{
lean_object* v_head_2976_; lean_object* v_tail_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_3001_; 
v_head_2976_ = lean_ctor_get(v_a_2973_, 0);
v_tail_2977_ = lean_ctor_get(v_a_2973_, 1);
v_isSharedCheck_3001_ = !lean_is_exclusive(v_a_2973_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2979_ = v_a_2973_;
v_isShared_2980_ = v_isSharedCheck_3001_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_tail_2977_);
lean_inc(v_head_2976_);
lean_dec(v_a_2973_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_3001_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___y_2982_; uint8_t v_hangingBy_2987_; 
v_hangingBy_2987_ = lean_ctor_get_uint8(v_head_2976_, sizeof(void*)*3 + 2);
if (v_hangingBy_2987_ == 0)
{
v___y_2982_ = v_head_2976_;
goto v___jp_2981_;
}
else
{
lean_object* v_ctxInfo_2988_; lean_object* v_tacticInfo_2989_; uint8_t v_useAfter_2990_; lean_object* v_priority_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3000_; 
v_ctxInfo_2988_ = lean_ctor_get(v_head_2976_, 0);
v_tacticInfo_2989_ = lean_ctor_get(v_head_2976_, 1);
v_useAfter_2990_ = lean_ctor_get_uint8(v_head_2976_, sizeof(void*)*3);
v_priority_2991_ = lean_ctor_get(v_head_2976_, 2);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_head_2976_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2993_ = v_head_2976_;
v_isShared_2994_ = v_isSharedCheck_3000_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_priority_2991_);
lean_inc(v_tacticInfo_2989_);
lean_inc(v_ctxInfo_2988_);
lean_dec(v_head_2976_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3000_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
uint8_t v___x_2995_; uint8_t v___x_2996_; lean_object* v___x_2998_; 
v___x_2995_ = lean_nat_dec_le(v_hoverCol_2971_, v_col_2972_);
v___x_2996_ = 0;
if (v_isShared_2994_ == 0)
{
v___x_2998_ = v___x_2993_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_ctxInfo_2988_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v_tacticInfo_2989_);
lean_ctor_set(v_reuseFailAlloc_2999_, 2, v_priority_2991_);
lean_ctor_set_uint8(v_reuseFailAlloc_2999_, sizeof(void*)*3, v_useAfter_2990_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
lean_ctor_set_uint8(v___x_2998_, sizeof(void*)*3 + 1, v___x_2995_);
lean_ctor_set_uint8(v___x_2998_, sizeof(void*)*3 + 2, v___x_2996_);
v___y_2982_ = v___x_2998_;
goto v___jp_2981_;
}
}
}
v___jp_2981_:
{
lean_object* v___x_2984_; 
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 1, v_a_2974_);
lean_ctor_set(v___x_2979_, 0, v___y_2982_);
v___x_2984_ = v___x_2979_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___y_2982_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_a_2974_);
v___x_2984_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
v_a_2973_ = v_tail_2977_;
v_a_2974_ = v___x_2984_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0___boxed(lean_object* v_hoverCol_3002_, lean_object* v_col_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(v_hoverCol_3002_, v_col_3003_, v_a_3004_, v_a_3005_);
lean_dec(v_col_3003_);
lean_dec(v_hoverCol_3002_);
return v_res_3006_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(lean_object* v_x_3007_){
_start:
{
if (lean_obj_tag(v_x_3007_) == 0)
{
uint8_t v___x_3008_; 
v___x_3008_ = 1;
return v___x_3008_;
}
else
{
lean_object* v_head_3009_; uint8_t v_indented_3010_; 
v_head_3009_ = lean_ctor_get(v_x_3007_, 0);
v_indented_3010_ = lean_ctor_get_uint8(v_head_3009_, sizeof(void*)*3 + 1);
if (v_indented_3010_ == 0)
{
return v_indented_3010_;
}
else
{
lean_object* v_tail_3011_; 
v_tail_3011_ = lean_ctor_get(v_x_3007_, 1);
v_x_3007_ = v_tail_3011_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1___boxed(lean_object* v_x_3013_){
_start:
{
uint8_t v_res_3014_; lean_object* v_r_3015_; 
v_res_3014_ = l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(v_x_3013_);
lean_dec(v_x_3013_);
v_r_3015_ = lean_box(v_res_3014_);
return v_r_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0(lean_object* v_text_3016_, lean_object* v_column_3017_, lean_object* v_hoverPos_3018_, lean_object* v_ctx_3019_, lean_object* v_i_3020_, lean_object* v_cs_3021_, lean_object* v_gs_3022_){
_start:
{
if (lean_obj_tag(v_i_3020_) == 0)
{
lean_object* v_i_3023_; lean_object* v___x_3024_; 
v_i_3023_ = lean_ctor_get(v_i_3020_, 0);
v___x_3024_ = l_Lean_Elab_Info_pos_x3f(v_i_3020_);
if (lean_obj_tag(v___x_3024_) == 1)
{
lean_object* v_val_3025_; lean_object* v___x_3026_; 
v_val_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_val_3025_);
lean_dec_ref_known(v___x_3024_, 1);
v___x_3026_ = l_Lean_Elab_Info_tailPos_x3f(v_i_3020_);
if (lean_obj_tag(v___x_3026_) == 1)
{
lean_object* v_val_3027_; lean_object* v___x_3028_; lean_object* v_column_3029_; lean_object* v_source_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3076_; 
v_val_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc(v_val_3027_);
lean_dec_ref_known(v___x_3026_, 1);
lean_inc_ref(v_text_3016_);
v___x_3028_ = l_Lean_FileMap_toPosition(v_text_3016_, v_val_3025_);
v_column_3029_ = lean_ctor_get(v___x_3028_, 1);
lean_inc(v_column_3029_);
lean_dec_ref(v___x_3028_);
v_source_3030_ = lean_ctor_get(v_text_3016_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v_text_3016_);
if (v_isSharedCheck_3076_ == 0)
{
lean_object* v_unused_3077_; 
v_unused_3077_ = lean_ctor_get(v_text_3016_, 1);
lean_dec(v_unused_3077_);
v___x_3032_ = v_text_3016_;
v_isShared_3033_ = v_isSharedCheck_3076_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_source_3030_);
lean_dec(v_text_3016_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3076_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3034_; uint8_t v___y_3036_; uint8_t v___y_3037_; uint8_t v___y_3038_; lean_object* v___y_3039_; lean_object* v_gs_3044_; lean_object* v___x_3045_; lean_object* v_trailSize_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; uint8_t v_atEOF_3049_; uint8_t v___x_3050_; lean_object* v___x_3051_; uint8_t v___y_3053_; uint8_t v___y_3059_; uint8_t v___y_3065_; uint8_t v___y_3070_; lean_object* v___y_3072_; uint8_t v___x_3075_; 
v___x_3034_ = lean_box(0);
v_gs_3044_ = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(v_column_3017_, v_column_3029_, v_gs_3022_, v___x_3034_);
v___x_3045_ = l_Lean_Elab_Info_stx(v_i_3020_);
v_trailSize_3046_ = l_Lean_Syntax_getTrailingSize(v___x_3045_);
v___x_3047_ = lean_nat_add(v_val_3027_, v_trailSize_3046_);
v___x_3048_ = lean_string_utf8_byte_size(v_source_3030_);
lean_dec_ref(v_source_3030_);
v_atEOF_3049_ = lean_nat_dec_eq(v___x_3047_, v___x_3048_);
v___x_3050_ = lean_nat_dec_le(v_val_3025_, v_hoverPos_3018_);
v___x_3051_ = lean_unsigned_to_nat(1u);
v___x_3075_ = lean_nat_dec_le(v___x_3051_, v_trailSize_3046_);
if (v___x_3075_ == 0)
{
lean_dec(v_trailSize_3046_);
v___y_3072_ = v___x_3051_;
goto v___jp_3071_;
}
else
{
v___y_3072_ = v_trailSize_3046_;
goto v___jp_3071_;
}
v___jp_3035_:
{
lean_object* v___x_3040_; lean_object* v___x_3042_; 
lean_inc_ref(v_i_3023_);
v___x_3040_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3040_, 0, v_ctx_3019_);
lean_ctor_set(v___x_3040_, 1, v_i_3023_);
lean_ctor_set(v___x_3040_, 2, v___y_3039_);
lean_ctor_set_uint8(v___x_3040_, sizeof(void*)*3, v___y_3036_);
lean_ctor_set_uint8(v___x_3040_, sizeof(void*)*3 + 1, v___y_3038_);
lean_ctor_set_uint8(v___x_3040_, sizeof(void*)*3 + 2, v___y_3037_);
if (v_isShared_3033_ == 0)
{
lean_ctor_set_tag(v___x_3032_, 1);
lean_ctor_set(v___x_3032_, 1, v___x_3034_);
lean_ctor_set(v___x_3032_, 0, v___x_3040_);
v___x_3042_ = v___x_3032_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v___x_3040_);
lean_ctor_set(v_reuseFailAlloc_3043_, 1, v___x_3034_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
v___jp_3052_:
{
uint8_t v___x_3054_; uint8_t v___x_3055_; uint8_t v___x_3056_; 
v___x_3054_ = lean_nat_dec_lt(v_column_3017_, v_column_3029_);
lean_dec(v_column_3029_);
v___x_3055_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock(v___x_3045_);
v___x_3056_ = lean_nat_dec_eq(v_hoverPos_3018_, v___x_3047_);
lean_dec(v___x_3047_);
if (v___x_3056_ == 0)
{
v___y_3036_ = v___y_3053_;
v___y_3037_ = v___x_3055_;
v___y_3038_ = v___x_3054_;
v___y_3039_ = v___x_3051_;
goto v___jp_3035_;
}
else
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_unsigned_to_nat(0u);
v___y_3036_ = v___y_3053_;
v___y_3037_ = v___x_3055_;
v___y_3038_ = v___x_3054_;
v___y_3039_ = v___x_3057_;
goto v___jp_3035_;
}
}
v___jp_3058_:
{
if (v___y_3059_ == 0)
{
lean_dec(v___x_3047_);
lean_dec(v___x_3045_);
lean_del_object(v___x_3032_);
lean_dec(v_column_3029_);
lean_dec(v_val_3027_);
lean_dec(v_val_3025_);
lean_dec_ref(v_ctx_3019_);
return v_gs_3044_;
}
else
{
lean_object* v___x_3060_; uint8_t v___x_3061_; 
lean_dec(v_gs_3044_);
v___x_3060_ = lean_nat_add(v_val_3025_, v___x_3051_);
v___x_3061_ = lean_nat_dec_le(v___x_3060_, v_hoverPos_3018_);
lean_dec(v___x_3060_);
if (v___x_3061_ == 0)
{
lean_dec(v_val_3027_);
lean_dec(v_val_3025_);
v___y_3053_ = v___x_3061_;
goto v___jp_3052_;
}
else
{
uint8_t v___x_3062_; 
v___x_3062_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_3018_, v_val_3025_, v_val_3027_, v_cs_3021_);
lean_dec(v_val_3027_);
lean_dec(v_val_3025_);
if (v___x_3062_ == 0)
{
v___y_3053_ = v___y_3059_;
goto v___jp_3052_;
}
else
{
uint8_t v___x_3063_; 
v___x_3063_ = 0;
v___y_3053_ = v___x_3063_;
goto v___jp_3052_;
}
}
}
}
v___jp_3064_:
{
if (v___y_3065_ == 0)
{
lean_dec(v___x_3047_);
lean_dec(v___x_3045_);
lean_del_object(v___x_3032_);
lean_dec(v_column_3029_);
lean_dec(v_val_3027_);
lean_dec(v_val_3025_);
lean_dec_ref(v_ctx_3019_);
return v_gs_3044_;
}
else
{
uint8_t v___x_3066_; 
v___x_3066_ = l_List_isEmpty___redArg(v_gs_3044_);
if (v___x_3066_ == 0)
{
uint8_t v___x_3067_; 
v___x_3067_ = lean_nat_dec_le(v_val_3027_, v_hoverPos_3018_);
if (v___x_3067_ == 0)
{
v___y_3059_ = v___x_3067_;
goto v___jp_3058_;
}
else
{
uint8_t v___x_3068_; 
v___x_3068_ = l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(v_gs_3044_);
v___y_3059_ = v___x_3068_;
goto v___jp_3058_;
}
}
else
{
v___y_3059_ = v___x_3066_;
goto v___jp_3058_;
}
}
}
v___jp_3069_:
{
if (v___x_3050_ == 0)
{
v___y_3065_ = v___x_3050_;
goto v___jp_3064_;
}
else
{
v___y_3065_ = v___y_3070_;
goto v___jp_3064_;
}
}
v___jp_3071_:
{
lean_object* v___x_3073_; uint8_t v___x_3074_; 
v___x_3073_ = lean_nat_add(v_val_3027_, v___y_3072_);
lean_dec(v___y_3072_);
v___x_3074_ = lean_nat_dec_lt(v_hoverPos_3018_, v___x_3073_);
lean_dec(v___x_3073_);
if (v___x_3074_ == 0)
{
v___y_3070_ = v_atEOF_3049_;
goto v___jp_3069_;
}
else
{
v___y_3070_ = v___x_3074_;
goto v___jp_3069_;
}
}
}
}
else
{
lean_dec(v___x_3026_);
lean_dec(v_val_3025_);
lean_dec_ref(v_ctx_3019_);
lean_dec_ref(v_text_3016_);
return v_gs_3022_;
}
}
else
{
lean_dec(v___x_3024_);
lean_dec_ref(v_ctx_3019_);
lean_dec_ref(v_text_3016_);
return v_gs_3022_;
}
}
else
{
lean_dec_ref(v_ctx_3019_);
lean_dec_ref(v_text_3016_);
return v_gs_3022_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0___boxed(lean_object* v_text_3078_, lean_object* v_column_3079_, lean_object* v_hoverPos_3080_, lean_object* v_ctx_3081_, lean_object* v_i_3082_, lean_object* v_cs_3083_, lean_object* v_gs_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0(v_text_3078_, v_column_3079_, v_hoverPos_3080_, v_ctx_3081_, v_i_3082_, v_cs_3083_, v_gs_3084_);
lean_dec_ref(v_cs_3083_);
lean_dec_ref(v_i_3082_);
lean_dec(v_hoverPos_3080_);
lean_dec(v_column_3079_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3_spec__3(lean_object* v_x_3086_, lean_object* v_x_3087_){
_start:
{
if (lean_obj_tag(v_x_3087_) == 0)
{
lean_inc(v_x_3086_);
return v_x_3086_;
}
else
{
lean_object* v_head_3088_; lean_object* v_tail_3089_; uint8_t v___x_3090_; 
v_head_3088_ = lean_ctor_get(v_x_3087_, 0);
v_tail_3089_ = lean_ctor_get(v_x_3087_, 1);
v___x_3090_ = lean_nat_dec_le(v_x_3086_, v_head_3088_);
if (v___x_3090_ == 0)
{
v_x_3087_ = v_tail_3089_;
goto _start;
}
else
{
v_x_3086_ = v_head_3088_;
v_x_3087_ = v_tail_3089_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3_spec__3___boxed(lean_object* v_x_3093_, lean_object* v_x_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3_spec__3(v_x_3093_, v_x_3094_);
lean_dec(v_x_3094_);
lean_dec(v_x_3093_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(lean_object* v_x_3096_){
_start:
{
if (lean_obj_tag(v_x_3096_) == 0)
{
lean_object* v___x_3097_; 
v___x_3097_ = lean_box(0);
return v___x_3097_;
}
else
{
lean_object* v_head_3098_; lean_object* v_tail_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v_head_3098_ = lean_ctor_get(v_x_3096_, 0);
v_tail_3099_ = lean_ctor_get(v_x_3096_, 1);
v___x_3100_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3_spec__3(v_head_3098_, v_tail_3099_);
v___x_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3100_);
return v___x_3101_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3___boxed(lean_object* v_x_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(v_x_3102_);
lean_dec(v_x_3102_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2(lean_object* v_a_3104_, lean_object* v_a_3105_){
_start:
{
if (lean_obj_tag(v_a_3104_) == 0)
{
lean_object* v___x_3106_; 
v___x_3106_ = l_List_reverse___redArg(v_a_3105_);
return v___x_3106_;
}
else
{
lean_object* v_head_3107_; lean_object* v_tail_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3117_; 
v_head_3107_ = lean_ctor_get(v_a_3104_, 0);
v_tail_3108_ = lean_ctor_get(v_a_3104_, 1);
v_isSharedCheck_3117_ = !lean_is_exclusive(v_a_3104_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3110_ = v_a_3104_;
v_isShared_3111_ = v_isSharedCheck_3117_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_tail_3108_);
lean_inc(v_head_3107_);
lean_dec(v_a_3104_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3117_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v_priority_3112_; lean_object* v___x_3114_; 
v_priority_3112_ = lean_ctor_get(v_head_3107_, 2);
lean_inc(v_priority_3112_);
lean_dec(v_head_3107_);
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 1, v_a_3105_);
lean_ctor_set(v___x_3110_, 0, v_priority_3112_);
v___x_3114_ = v___x_3110_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_priority_3112_);
lean_ctor_set(v_reuseFailAlloc_3116_, 1, v_a_3105_);
v___x_3114_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
v_a_3104_ = v_tail_3108_;
v_a_3105_ = v___x_3114_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__5(lean_object* v_maxPrio_x3f_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_){
_start:
{
if (lean_obj_tag(v_a_3119_) == 0)
{
lean_object* v___x_3121_; 
v___x_3121_ = l_List_reverse___redArg(v_a_3120_);
return v___x_3121_;
}
else
{
lean_object* v_head_3122_; lean_object* v_tail_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3135_; 
v_head_3122_ = lean_ctor_get(v_a_3119_, 0);
v_tail_3123_ = lean_ctor_get(v_a_3119_, 1);
v_isSharedCheck_3135_ = !lean_is_exclusive(v_a_3119_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3125_ = v_a_3119_;
v_isShared_3126_ = v_isSharedCheck_3135_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_tail_3123_);
lean_inc(v_head_3122_);
lean_dec(v_a_3119_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3135_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v_priority_3127_; lean_object* v___x_3128_; uint8_t v___x_3129_; 
v_priority_3127_ = lean_ctor_get(v_head_3122_, 2);
lean_inc(v_priority_3127_);
v___x_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3128_, 0, v_priority_3127_);
v___x_3129_ = l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(v___x_3128_, v_maxPrio_x3f_3118_);
lean_dec_ref_known(v___x_3128_, 1);
if (v___x_3129_ == 0)
{
lean_del_object(v___x_3125_);
lean_dec(v_head_3122_);
v_a_3119_ = v_tail_3123_;
goto _start;
}
else
{
lean_object* v___x_3132_; 
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 1, v_a_3120_);
v___x_3132_ = v___x_3125_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_head_3122_);
lean_ctor_set(v_reuseFailAlloc_3134_, 1, v_a_3120_);
v___x_3132_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
v_a_3119_ = v_tail_3123_;
v_a_3120_ = v___x_3132_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__5___boxed(lean_object* v_maxPrio_x3f_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__5(v_maxPrio_x3f_3136_, v_a_3137_, v_a_3138_);
lean_dec(v_maxPrio_x3f_3136_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f(lean_object* v_text_3140_, lean_object* v_t_3141_, lean_object* v_hoverPos_3142_){
_start:
{
lean_object* v___x_3143_; lean_object* v_column_3144_; lean_object* v___f_3145_; lean_object* v_gs_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v_maxPrio_x3f_3149_; lean_object* v___x_3150_; 
lean_inc_ref(v_text_3140_);
v___x_3143_ = l_Lean_FileMap_toPosition(v_text_3140_, v_hoverPos_3142_);
v_column_3144_ = lean_ctor_get(v___x_3143_, 1);
lean_inc(v_column_3144_);
lean_dec_ref(v___x_3143_);
v___f_3145_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0___boxed), 7, 3);
lean_closure_set(v___f_3145_, 0, v_text_3140_);
lean_closure_set(v___f_3145_, 1, v_column_3144_);
lean_closure_set(v___f_3145_, 2, v_hoverPos_3142_);
v_gs_3146_ = l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg(v___f_3145_, v_t_3141_);
v___x_3147_ = lean_box(0);
lean_inc(v_gs_3146_);
v___x_3148_ = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2(v_gs_3146_, v___x_3147_);
v_maxPrio_x3f_3149_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(v___x_3148_);
lean_dec(v___x_3148_);
v___x_3150_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__5(v_maxPrio_x3f_3149_, v_gs_3146_, v___x_3147_);
lean_dec(v_maxPrio_x3f_3149_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(lean_object* v___x_3151_, uint8_t v___y_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_){
_start:
{
if (lean_obj_tag(v_a_3153_) == 0)
{
lean_object* v___x_3155_; 
v___x_3155_ = l_List_reverse___redArg(v_a_3154_);
return v___x_3155_;
}
else
{
lean_object* v_head_3156_; lean_object* v_snd_3157_; lean_object* v_tail_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3173_; 
v_head_3156_ = lean_ctor_get(v_a_3153_, 0);
lean_inc(v_head_3156_);
v_snd_3157_ = lean_ctor_get(v_head_3156_, 1);
v_tail_3158_ = lean_ctor_get(v_a_3153_, 1);
v_isSharedCheck_3173_ = !lean_is_exclusive(v_a_3153_);
if (v_isSharedCheck_3173_ == 0)
{
lean_object* v_unused_3174_; 
v_unused_3174_ = lean_ctor_get(v_a_3153_, 0);
lean_dec(v_unused_3174_);
v___x_3160_ = v_a_3153_;
v_isShared_3161_ = v_isSharedCheck_3173_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_tail_3158_);
lean_dec(v_a_3153_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3173_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v_info_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; uint8_t v___x_3166_; 
v_info_3162_ = lean_ctor_get(v_snd_3157_, 1);
v___x_3163_ = l_Lean_Elab_Info_stx(v_info_3162_);
v___x_3164_ = lean_unsigned_to_nat(0u);
v___x_3165_ = l_Lean_Syntax_getArg(v___x_3151_, v___x_3164_);
v___x_3166_ = l_Lean_Syntax_structEq(v___x_3163_, v___x_3165_);
lean_dec(v___x_3165_);
lean_dec(v___x_3163_);
if (v___x_3166_ == 0)
{
if (v___y_3152_ == 0)
{
lean_del_object(v___x_3160_);
lean_dec(v_head_3156_);
v_a_3153_ = v_tail_3158_;
goto _start;
}
else
{
lean_object* v___x_3169_; 
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 1, v_a_3154_);
v___x_3169_ = v___x_3160_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_head_3156_);
lean_ctor_set(v_reuseFailAlloc_3171_, 1, v_a_3154_);
v___x_3169_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
v_a_3153_ = v_tail_3158_;
v_a_3154_ = v___x_3169_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_3160_);
lean_dec(v_head_3156_);
v_a_3153_ = v_tail_3158_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0___boxed(lean_object* v___x_3175_, lean_object* v___y_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_){
_start:
{
uint8_t v___y_1198__boxed_3179_; lean_object* v_res_3180_; 
v___y_1198__boxed_3179_ = lean_unbox(v___y_3176_);
v_res_3180_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(v___x_3175_, v___y_1198__boxed_3179_, v_a_3177_, v_a_3178_);
lean_dec(v___x_3175_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0(lean_object* v_ctx_3187_, lean_object* v_info_3188_, lean_object* v_children_3189_, lean_object* v_results_3190_){
_start:
{
lean_object* v___x_3191_; uint8_t v___y_3193_; lean_object* v___x_3196_; uint8_t v___x_3197_; 
v___x_3191_ = l_Lean_Elab_Info_stx(v_info_3188_);
v___x_3196_ = ((lean_object*)(l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1));
lean_inc(v___x_3191_);
v___x_3197_ = l_Lean_Syntax_isOfKind(v___x_3191_, v___x_3196_);
if (v___x_3197_ == 0)
{
v___y_3193_ = v___x_3197_;
goto v___jp_3192_;
}
else
{
lean_object* v___x_3198_; lean_object* v___x_3199_; uint8_t v___x_3200_; 
v___x_3198_ = lean_unsigned_to_nat(0u);
v___x_3199_ = l_Lean_Syntax_getArg(v___x_3191_, v___x_3198_);
v___x_3200_ = l_Lean_Syntax_isIdent(v___x_3199_);
lean_dec(v___x_3199_);
v___y_3193_ = v___x_3200_;
goto v___jp_3192_;
}
v___jp_3192_:
{
if (v___y_3193_ == 0)
{
lean_dec(v___x_3191_);
return v_results_3190_;
}
else
{
lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3194_ = lean_box(0);
v___x_3195_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(v___x_3191_, v___y_3193_, v_results_3190_, v___x_3194_);
lean_dec(v___x_3191_);
return v___x_3195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___boxed(lean_object* v_ctx_3201_, lean_object* v_info_3202_, lean_object* v_children_3203_, lean_object* v_results_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0(v_ctx_3201_, v_info_3202_, v_children_3203_, v_results_3204_);
lean_dec_ref(v_children_3203_);
lean_dec_ref(v_info_3202_);
lean_dec_ref(v_ctx_3201_);
return v_res_3205_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(lean_object* v_x_3206_, lean_object* v_x_3207_){
_start:
{
if (lean_obj_tag(v_x_3206_) == 0)
{
if (lean_obj_tag(v_x_3207_) == 0)
{
uint8_t v___x_3208_; 
v___x_3208_ = 1;
return v___x_3208_;
}
else
{
uint8_t v___x_3209_; 
v___x_3209_ = 0;
return v___x_3209_;
}
}
else
{
if (lean_obj_tag(v_x_3207_) == 0)
{
uint8_t v___x_3210_; 
v___x_3210_ = 0;
return v___x_3210_;
}
else
{
lean_object* v_val_3211_; lean_object* v_val_3212_; uint8_t v___x_3213_; 
v_val_3211_ = lean_ctor_get(v_x_3206_, 0);
v_val_3212_ = lean_ctor_get(v_x_3207_, 0);
v___x_3213_ = l_Lean_Elab_instBEqHoverableInfoPrio_beq(v_val_3211_, v_val_3212_);
return v___x_3213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4___boxed(lean_object* v_x_3214_, lean_object* v_x_3215_){
_start:
{
uint8_t v_res_3216_; lean_object* v_r_3217_; 
v_res_3216_ = l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(v_x_3214_, v_x_3215_);
lean_dec(v_x_3215_);
lean_dec(v_x_3214_);
v_r_3217_ = lean_box(v_res_3216_);
return v_r_3217_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5(lean_object* v_maxPrio_x3f_3218_, lean_object* v_x_3219_){
_start:
{
if (lean_obj_tag(v_x_3219_) == 0)
{
lean_object* v___x_3220_; 
v___x_3220_ = lean_box(0);
return v___x_3220_;
}
else
{
lean_object* v_head_3221_; lean_object* v_tail_3222_; lean_object* v_fst_3223_; lean_object* v___x_3224_; uint8_t v___x_3225_; 
v_head_3221_ = lean_ctor_get(v_x_3219_, 0);
v_tail_3222_ = lean_ctor_get(v_x_3219_, 1);
v_fst_3223_ = lean_ctor_get(v_head_3221_, 0);
lean_inc(v_fst_3223_);
v___x_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3224_, 0, v_fst_3223_);
v___x_3225_ = l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(v___x_3224_, v_maxPrio_x3f_3218_);
lean_dec_ref_known(v___x_3224_, 1);
if (v___x_3225_ == 0)
{
v_x_3219_ = v_tail_3222_;
goto _start;
}
else
{
lean_object* v___x_3227_; 
lean_inc(v_head_3221_);
v___x_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3227_, 0, v_head_3221_);
return v___x_3227_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5___boxed(lean_object* v_maxPrio_x3f_3228_, lean_object* v_x_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5(v_maxPrio_x3f_3228_, v_x_3229_);
lean_dec(v_x_3229_);
lean_dec(v_maxPrio_x3f_3228_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(lean_object* v_x_3231_, lean_object* v_x_3232_){
_start:
{
if (lean_obj_tag(v_x_3232_) == 0)
{
lean_inc_ref(v_x_3231_);
return v_x_3231_;
}
else
{
lean_object* v_head_3233_; lean_object* v_tail_3234_; uint8_t v___x_3235_; 
v_head_3233_ = lean_ctor_get(v_x_3232_, 0);
v_tail_3234_ = lean_ctor_get(v_x_3232_, 1);
v___x_3235_ = l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(v_x_3231_, v_head_3233_);
if (v___x_3235_ == 2)
{
v_x_3232_ = v_tail_3234_;
goto _start;
}
else
{
v_x_3231_ = v_head_3233_;
v_x_3232_ = v_tail_3234_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4___boxed(lean_object* v_x_3238_, lean_object* v_x_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(v_x_3238_, v_x_3239_);
lean_dec(v_x_3239_);
lean_dec_ref(v_x_3238_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(lean_object* v_x_3241_){
_start:
{
if (lean_obj_tag(v_x_3241_) == 0)
{
lean_object* v___x_3242_; 
v___x_3242_ = lean_box(0);
return v___x_3242_;
}
else
{
lean_object* v_head_3243_; lean_object* v_tail_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v_head_3243_ = lean_ctor_get(v_x_3241_, 0);
v_tail_3244_ = lean_ctor_get(v_x_3241_, 1);
v___x_3245_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(v_head_3243_, v_tail_3244_);
v___x_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3245_);
return v___x_3246_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3___boxed(lean_object* v_x_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(v_x_3247_);
lean_dec(v_x_3247_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__1(lean_object* v_a_3249_, lean_object* v_a_3250_){
_start:
{
if (lean_obj_tag(v_a_3249_) == 0)
{
lean_object* v___x_3251_; 
v___x_3251_ = lean_array_to_list(v_a_3250_);
return v___x_3251_;
}
else
{
lean_object* v_head_3252_; 
v_head_3252_ = lean_ctor_get(v_a_3249_, 0);
if (lean_obj_tag(v_head_3252_) == 0)
{
lean_object* v_tail_3253_; 
v_tail_3253_ = lean_ctor_get(v_a_3249_, 1);
lean_inc(v_tail_3253_);
lean_dec_ref_known(v_a_3249_, 2);
v_a_3249_ = v_tail_3253_;
goto _start;
}
else
{
lean_object* v_val_3255_; 
v_val_3255_ = lean_ctor_get(v_head_3252_, 0);
if (lean_obj_tag(v_val_3255_) == 0)
{
lean_object* v_tail_3256_; 
v_tail_3256_ = lean_ctor_get(v_a_3249_, 1);
lean_inc(v_tail_3256_);
lean_dec_ref_known(v_a_3249_, 2);
v_a_3249_ = v_tail_3256_;
goto _start;
}
else
{
lean_object* v_tail_3258_; lean_object* v_val_3259_; lean_object* v___x_3260_; 
lean_inc_ref(v_val_3255_);
v_tail_3258_ = lean_ctor_get(v_a_3249_, 1);
lean_inc(v_tail_3258_);
lean_dec_ref_known(v_a_3249_, 2);
v_val_3259_ = lean_ctor_get(v_val_3255_, 0);
lean_inc(v_val_3259_);
lean_dec_ref_known(v_val_3255_, 1);
v___x_3260_ = lean_array_push(v_a_3250_, v_val_3259_);
v_a_3249_ = v_tail_3258_;
v_a_3250_ = v___x_3260_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__2(lean_object* v_a_3262_, lean_object* v_a_3263_){
_start:
{
if (lean_obj_tag(v_a_3262_) == 0)
{
lean_object* v___x_3264_; 
v___x_3264_ = l_List_reverse___redArg(v_a_3263_);
return v___x_3264_;
}
else
{
lean_object* v_head_3265_; lean_object* v_tail_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3275_; 
v_head_3265_ = lean_ctor_get(v_a_3262_, 0);
v_tail_3266_ = lean_ctor_get(v_a_3262_, 1);
v_isSharedCheck_3275_ = !lean_is_exclusive(v_a_3262_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3268_ = v_a_3262_;
v_isShared_3269_ = v_isSharedCheck_3275_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_tail_3266_);
lean_inc(v_head_3265_);
lean_dec(v_a_3262_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3275_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v_fst_3270_; lean_object* v___x_3272_; 
v_fst_3270_ = lean_ctor_get(v_head_3265_, 0);
lean_inc(v_fst_3270_);
lean_dec(v_head_3265_);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 1, v_a_3263_);
lean_ctor_set(v___x_3268_, 0, v_fst_3270_);
v___x_3272_ = v___x_3268_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_fst_3270_);
lean_ctor_set(v_reuseFailAlloc_3274_, 1, v_a_3263_);
v___x_3272_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
v_a_3262_ = v_tail_3266_;
v_a_3263_ = v___x_3272_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1(lean_object* v_filter_3276_, lean_object* v_hoverPos_3277_, uint8_t v_includeStop_3278_, lean_object* v_ctx_3279_, lean_object* v_info_3280_, lean_object* v_children_3281_, lean_object* v_results_3282_){
_start:
{
uint8_t v___y_3284_; lean_object* v___y_3285_; uint8_t v___y_3286_; uint8_t v___y_3287_; uint8_t v___y_3293_; lean_object* v___y_3294_; uint8_t v___y_3295_; uint8_t v___y_3296_; uint8_t v___y_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v_maxPrio_x3f_3303_; lean_object* v_bestResult_x3f_3304_; 
v___x_3298_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___closed__0));
v___x_3299_ = l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__1(v_results_3282_, v___x_3298_);
lean_inc_ref(v_children_3281_);
lean_inc_ref(v_info_3280_);
lean_inc_ref(v_ctx_3279_);
v___x_3300_ = lean_apply_4(v_filter_3276_, v_ctx_3279_, v_info_3280_, v_children_3281_, v___x_3299_);
v___x_3301_ = lean_box(0);
lean_inc(v___x_3300_);
v___x_3302_ = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__2(v___x_3300_, v___x_3301_);
v_maxPrio_x3f_3303_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(v___x_3302_);
lean_dec(v___x_3302_);
v_bestResult_x3f_3304_ = l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5(v_maxPrio_x3f_3303_, v___x_3300_);
lean_dec(v___x_3300_);
lean_dec(v_maxPrio_x3f_3303_);
if (lean_obj_tag(v_bestResult_x3f_3304_) == 1)
{
lean_dec_ref(v_children_3281_);
lean_dec_ref(v_info_3280_);
lean_dec_ref(v_ctx_3279_);
return v_bestResult_x3f_3304_;
}
else
{
lean_object* v___x_3305_; uint8_t v___y_3307_; uint8_t v___y_3308_; uint8_t v___y_3309_; uint8_t v___y_3323_; lean_object* v___x_3327_; uint8_t v___x_3328_; 
lean_dec(v_bestResult_x3f_3304_);
v___x_3305_ = l_Lean_Elab_Info_stx(v_info_3280_);
v___x_3327_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__1));
lean_inc(v___x_3305_);
v___x_3328_ = l_Lean_Syntax_isOfKind(v___x_3305_, v___x_3327_);
if (v___x_3328_ == 0)
{
lean_object* v___x_3329_; 
lean_inc_ref(v_info_3280_);
v___x_3329_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_3280_);
if (lean_obj_tag(v___x_3329_) == 0)
{
v___y_3323_ = v___x_3328_;
goto v___jp_3322_;
}
else
{
lean_object* v_val_3330_; lean_object* v_elaborator_3331_; lean_object* v___x_3332_; uint8_t v___x_3333_; 
v_val_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_val_3330_);
lean_dec_ref_known(v___x_3329_, 1);
v_elaborator_3331_ = lean_ctor_get(v_val_3330_, 0);
lean_inc(v_elaborator_3331_);
lean_dec(v_val_3330_);
v___x_3332_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6));
v___x_3333_ = lean_name_eq(v_elaborator_3331_, v___x_3332_);
lean_dec(v_elaborator_3331_);
v___y_3323_ = v___x_3333_;
goto v___jp_3322_;
}
}
else
{
v___y_3323_ = v___x_3328_;
goto v___jp_3322_;
}
v___jp_3306_:
{
lean_object* v___x_3310_; 
v___x_3310_ = l_Lean_Syntax_getRange_x3f(v___x_3305_, v___y_3307_);
lean_dec(v___x_3305_);
if (lean_obj_tag(v___x_3310_) == 1)
{
lean_object* v_val_3311_; uint8_t v___x_3312_; 
v_val_3311_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_val_3311_);
lean_dec_ref_known(v___x_3310_, 1);
v___x_3312_ = l_Lean_Syntax_Range_contains(v_val_3311_, v_hoverPos_3277_, v_includeStop_3278_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; 
lean_dec(v_val_3311_);
lean_dec_ref(v_children_3281_);
lean_dec_ref(v_info_3280_);
lean_dec_ref(v_ctx_3279_);
v___x_3313_ = lean_box(0);
return v___x_3313_;
}
else
{
if (v___y_3309_ == 0)
{
lean_object* v___x_3314_; 
lean_dec(v_val_3311_);
lean_dec_ref(v_children_3281_);
lean_dec_ref(v_info_3280_);
lean_dec_ref(v_ctx_3279_);
v___x_3314_ = lean_box(0);
return v___x_3314_;
}
else
{
lean_object* v_start_3315_; lean_object* v_stop_3316_; uint8_t v_decide_3317_; lean_object* v___x_3318_; 
v_start_3315_ = lean_ctor_get(v_val_3311_, 0);
lean_inc(v_start_3315_);
v_stop_3316_ = lean_ctor_get(v_val_3311_, 1);
lean_inc(v_stop_3316_);
lean_dec(v_val_3311_);
v_decide_3317_ = lean_nat_dec_eq(v_stop_3316_, v_hoverPos_3277_);
v___x_3318_ = lean_nat_sub(v_stop_3316_, v_start_3315_);
lean_dec(v_start_3315_);
lean_dec(v_stop_3316_);
if (lean_obj_tag(v_info_3280_) == 1)
{
lean_object* v_i_3319_; lean_object* v_expr_3320_; 
v_i_3319_ = lean_ctor_get(v_info_3280_, 0);
v_expr_3320_ = lean_ctor_get(v_i_3319_, 3);
if (lean_obj_tag(v_expr_3320_) == 1)
{
v___y_3293_ = v___y_3307_;
v___y_3294_ = v___x_3318_;
v___y_3295_ = v___y_3308_;
v___y_3296_ = v_decide_3317_;
v___y_3297_ = v___y_3307_;
goto v___jp_3292_;
}
else
{
v___y_3293_ = v___y_3307_;
v___y_3294_ = v___x_3318_;
v___y_3295_ = v___y_3308_;
v___y_3296_ = v_decide_3317_;
v___y_3297_ = v___y_3308_;
goto v___jp_3292_;
}
}
else
{
v___y_3293_ = v___y_3307_;
v___y_3294_ = v___x_3318_;
v___y_3295_ = v___y_3308_;
v___y_3296_ = v_decide_3317_;
v___y_3297_ = v___y_3308_;
goto v___jp_3292_;
}
}
}
}
else
{
lean_object* v___x_3321_; 
lean_dec(v___x_3310_);
lean_dec_ref(v_children_3281_);
lean_dec_ref(v_info_3280_);
lean_dec_ref(v_ctx_3279_);
v___x_3321_ = lean_box(0);
return v___x_3321_;
}
}
v___jp_3322_:
{
if (v___y_3323_ == 0)
{
uint8_t v___x_3324_; 
v___x_3324_ = 1;
switch(lean_obj_tag(v_info_3280_))
{
case 7:
{
v___y_3307_ = v___x_3324_;
v___y_3308_ = v___y_3323_;
v___y_3309_ = v___x_3324_;
goto v___jp_3306_;
}
case 5:
{
v___y_3307_ = v___x_3324_;
v___y_3308_ = v___y_3323_;
v___y_3309_ = v___x_3324_;
goto v___jp_3306_;
}
case 6:
{
v___y_3307_ = v___x_3324_;
v___y_3308_ = v___y_3323_;
v___y_3309_ = v___x_3324_;
goto v___jp_3306_;
}
default: 
{
lean_object* v___x_3325_; 
lean_inc_ref(v_info_3280_);
v___x_3325_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_3280_);
if (lean_obj_tag(v___x_3325_) == 0)
{
v___y_3307_ = v___x_3324_;
v___y_3308_ = v___y_3323_;
v___y_3309_ = v___y_3323_;
goto v___jp_3306_;
}
else
{
lean_dec_ref_known(v___x_3325_, 1);
v___y_3307_ = v___x_3324_;
v___y_3308_ = v___y_3323_;
v___y_3309_ = v___x_3324_;
goto v___jp_3306_;
}
}
}
}
else
{
lean_object* v___x_3326_; 
lean_dec(v___x_3305_);
lean_dec_ref(v_children_3281_);
lean_dec_ref(v_info_3280_);
lean_dec_ref(v_ctx_3279_);
v___x_3326_ = lean_box(0);
return v___x_3326_;
}
}
}
v___jp_3283_:
{
lean_object* v_priority_3288_; lean_object* v_result_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v_priority_3288_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_priority_3288_, 0, v___y_3285_);
lean_ctor_set_uint8(v_priority_3288_, sizeof(void*)*1, v___y_3286_);
lean_ctor_set_uint8(v_priority_3288_, sizeof(void*)*1 + 1, v___y_3284_);
lean_ctor_set_uint8(v_priority_3288_, sizeof(void*)*1 + 2, v___y_3287_);
v_result_3289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_result_3289_, 0, v_ctx_3279_);
lean_ctor_set(v_result_3289_, 1, v_info_3280_);
lean_ctor_set(v_result_3289_, 2, v_children_3281_);
v___x_3290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3290_, 0, v_priority_3288_);
lean_ctor_set(v___x_3290_, 1, v_result_3289_);
v___x_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3290_);
return v___x_3291_;
}
v___jp_3292_:
{
if (lean_obj_tag(v_info_3280_) == 2)
{
v___y_3284_ = v___y_3297_;
v___y_3285_ = v___y_3294_;
v___y_3286_ = v___y_3296_;
v___y_3287_ = v___y_3293_;
goto v___jp_3283_;
}
else
{
v___y_3284_ = v___y_3297_;
v___y_3285_ = v___y_3294_;
v___y_3286_ = v___y_3296_;
v___y_3287_ = v___y_3295_;
goto v___jp_3283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1___boxed(lean_object* v_filter_3334_, lean_object* v_hoverPos_3335_, lean_object* v_includeStop_3336_, lean_object* v_ctx_3337_, lean_object* v_info_3338_, lean_object* v_children_3339_, lean_object* v_results_3340_){
_start:
{
uint8_t v_includeStop_boxed_3341_; lean_object* v_res_3342_; 
v_includeStop_boxed_3341_ = lean_unbox(v_includeStop_3336_);
v_res_3342_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1(v_filter_3334_, v_hoverPos_3335_, v_includeStop_boxed_3341_, v_ctx_3337_, v_info_3338_, v_children_3339_, v_results_3340_);
lean_dec(v_hoverPos_3335_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(lean_object* v_t_3343_, lean_object* v_hoverPos_3344_, uint8_t v_includeStop_3345_, lean_object* v_filter_3346_){
_start:
{
lean_object* v___f_3347_; lean_object* v___x_3348_; lean_object* v_postNode_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___f_3347_ = ((lean_object*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___closed__0));
v___x_3348_ = lean_box(v_includeStop_3345_);
v_postNode_3349_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1___boxed), 7, 3);
lean_closure_set(v_postNode_3349_, 0, v_filter_3346_);
lean_closure_set(v_postNode_3349_, 1, v_hoverPos_3344_);
lean_closure_set(v_postNode_3349_, 2, v___x_3348_);
v___x_3350_ = lean_box(0);
v___x_3351_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v___f_3347_, v_postNode_3349_, v___x_3350_, v_t_3343_);
if (lean_obj_tag(v___x_3351_) == 0)
{
return v___x_3350_;
}
else
{
lean_object* v_val_3352_; 
v_val_3352_ = lean_ctor_get(v___x_3351_, 0);
lean_inc(v_val_3352_);
lean_dec_ref_known(v___x_3351_, 1);
if (lean_obj_tag(v_val_3352_) == 0)
{
return v___x_3350_;
}
else
{
lean_object* v_val_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3365_; 
v_val_3353_ = lean_ctor_get(v_val_3352_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v_val_3352_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3355_ = v_val_3352_;
v_isShared_3356_ = v_isSharedCheck_3365_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_val_3353_);
lean_dec(v_val_3352_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3365_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v_snd_3357_; lean_object* v_info_3358_; lean_object* v___x_3360_; 
v_snd_3357_ = lean_ctor_get(v_val_3353_, 1);
lean_inc(v_snd_3357_);
lean_dec(v_val_3353_);
v_info_3358_ = lean_ctor_get(v_snd_3357_, 1);
lean_inc_ref(v_info_3358_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v_snd_3357_);
v___x_3360_ = v___x_3355_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_snd_3357_);
v___x_3360_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
if (lean_obj_tag(v_info_3358_) == 1)
{
lean_object* v_i_3361_; lean_object* v_expr_3362_; uint8_t v___x_3363_; 
v_i_3361_ = lean_ctor_get(v_info_3358_, 0);
lean_inc_ref(v_i_3361_);
lean_dec_ref_known(v_info_3358_, 1);
v_expr_3362_ = lean_ctor_get(v_i_3361_, 3);
lean_inc_ref(v_expr_3362_);
lean_dec_ref(v_i_3361_);
v___x_3363_ = l_Lean_Expr_isSyntheticSorry(v_expr_3362_);
lean_dec_ref(v_expr_3362_);
if (v___x_3363_ == 0)
{
return v___x_3360_;
}
else
{
lean_dec_ref(v___x_3360_);
return v___x_3350_;
}
}
else
{
lean_dec_ref(v_info_3358_);
return v___x_3360_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___boxed(lean_object* v_t_3366_, lean_object* v_hoverPos_3367_, lean_object* v_includeStop_3368_, lean_object* v_filter_3369_){
_start:
{
uint8_t v_includeStop_boxed_3370_; lean_object* v_res_3371_; 
v_includeStop_boxed_3370_ = lean_unbox(v_includeStop_3368_);
v_res_3371_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(v_t_3366_, v_hoverPos_3367_, v_includeStop_boxed_3370_, v_filter_3369_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f(lean_object* v_t_3373_, lean_object* v_hoverPos_3374_){
_start:
{
lean_object* v_filter_3375_; uint8_t v___x_3376_; lean_object* v___x_3377_; 
v_filter_3375_ = ((lean_object*)(l_Lean_Elab_InfoTree_termGoalAt_x3f___closed__0));
v___x_3376_ = 1;
v___x_3377_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(v_t_3373_, v_hoverPos_3374_, v___x_3376_, v_filter_3375_);
return v___x_3377_;
}
}
lean_object* runtime_initialize_Lean_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_InfoTree_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_InfoTree_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_DocString(uint8_t builtin);
lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_InfoTree_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_InfoTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_InfoTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_InfoTree_Util(builtin);
}
#ifdef __cplusplus
}
#endif
