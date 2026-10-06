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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_LocalContext_findFVar_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_instBEqOption_beq___redArg(lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Syntax_isToken(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4___boxed(lean_object*, lean_object*);
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
v___x_1357_ = l_instBEqOption_beq___redArg(v___x_1352_, v___x_1356_, v_maxPrio_x3f_1353_);
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
uint8_t v___y_1386_; uint8_t v___y_1387_; lean_object* v___y_1388_; uint8_t v___y_1389_; uint8_t v___y_1396_; uint8_t v___y_1397_; uint8_t v___y_1398_; lean_object* v___y_1399_; uint8_t v___y_1400_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v_maxPrio_x3f_1406_; lean_object* v___f_1407_; lean_object* v_bestResult_x3f_1408_; 
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
v___x_1415_ = l_Lean_Syntax_getRange_x3f(v___x_1410_, v___y_1413_);
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
v___y_1396_ = v_decide_1420_;
v___y_1397_ = v___y_1412_;
v___y_1398_ = v___y_1413_;
v___y_1399_ = v___x_1421_;
v___y_1400_ = v___y_1413_;
goto v___jp_1395_;
}
else
{
v___y_1396_ = v_decide_1420_;
v___y_1397_ = v___y_1412_;
v___y_1398_ = v___y_1413_;
v___y_1399_ = v___x_1421_;
v___y_1400_ = v___y_1412_;
goto v___jp_1395_;
}
}
else
{
v___y_1396_ = v_decide_1420_;
v___y_1397_ = v___y_1412_;
v___y_1398_ = v___y_1413_;
v___y_1399_ = v___x_1421_;
v___y_1400_ = v___y_1412_;
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
v___y_1412_ = v___y_1427_;
v___y_1413_ = v___x_1428_;
v___y_1414_ = v___x_1428_;
goto v___jp_1411_;
}
case 5:
{
v___y_1412_ = v___y_1427_;
v___y_1413_ = v___x_1428_;
v___y_1414_ = v___x_1428_;
goto v___jp_1411_;
}
case 6:
{
v___y_1412_ = v___y_1427_;
v___y_1413_ = v___x_1428_;
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
v___y_1412_ = v___y_1427_;
v___y_1413_ = v___x_1428_;
v___y_1414_ = v___y_1427_;
goto v___jp_1411_;
}
else
{
lean_dec_ref_known(v___x_1429_, 1);
v___y_1412_ = v___y_1427_;
v___y_1413_ = v___x_1428_;
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
lean_ctor_set_uint8(v_priority_1390_, sizeof(void*)*1, v___y_1386_);
lean_ctor_set_uint8(v_priority_1390_, sizeof(void*)*1 + 1, v___y_1387_);
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
v___y_1386_ = v___y_1396_;
v___y_1387_ = v___y_1400_;
v___y_1388_ = v___y_1399_;
v___y_1389_ = v___y_1398_;
goto v___jp_1385_;
}
else
{
v___y_1386_ = v___y_1396_;
v___y_1387_ = v___y_1400_;
v___y_1388_ = v___y_1399_;
v___y_1389_ = v___y_1397_;
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
if (lean_obj_tag(v_a_1818_) == 1)
{
lean_dec(v_optionName_1814_);
return v___x_1817_;
}
else
{
lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1860_; 
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
if (lean_obj_tag(v_a_1753_) == 0)
{
lean_object* v___x_1754_; 
lean_dec_ref_known(v___x_1752_, 1);
v___x_1754_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_elaborator_1748_, v___x_1751_, v___y_1744_, v___y_1745_);
return v___x_1754_;
}
else
{
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
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1905_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1906_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1907_ = lean_unsigned_to_nat(0u);
v___x_1908_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
lean_ctor_set(v___x_1908_, 2, v___x_1907_);
lean_ctor_set(v___x_1908_, 3, v___x_1907_);
lean_ctor_set(v___x_1908_, 4, v___x_1906_);
lean_ctor_set(v___x_1908_, 5, v___x_1906_);
lean_ctor_set(v___x_1908_, 6, v___x_1906_);
lean_ctor_set(v___x_1908_, 7, v___x_1906_);
lean_ctor_set(v___x_1908_, 8, v___x_1906_);
lean_ctor_set(v___x_1908_, 9, v___x_1906_);
lean_ctor_set(v___x_1908_, 10, v___x_1906_);
lean_ctor_set(v___x_1908_, 11, v___x_1905_);
return v___x_1908_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = lean_unsigned_to_nat(32u);
v___x_1910_ = lean_mk_empty_array_with_capacity(v___x_1909_);
v___x_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
return v___x_1911_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1912_ = ((size_t)5ULL);
v___x_1913_ = lean_unsigned_to_nat(0u);
v___x_1914_ = lean_unsigned_to_nat(32u);
v___x_1915_ = lean_mk_empty_array_with_capacity(v___x_1914_);
v___x_1916_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1917_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
lean_ctor_set(v___x_1917_, 1, v___x_1915_);
lean_ctor_set(v___x_1917_, 2, v___x_1913_);
lean_ctor_set(v___x_1917_, 3, v___x_1913_);
lean_ctor_set_usize(v___x_1917_, 4, v___x_1912_);
return v___x_1917_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1918_ = lean_box(1);
v___x_1919_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_1920_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1921_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
lean_ctor_set(v___x_1921_, 1, v___x_1919_);
lean_ctor_set(v___x_1921_, 2, v___x_1918_);
return v___x_1921_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1924_ = l_Lean_stringToMessageData(v___x_1923_);
return v___x_1924_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1927_ = l_Lean_stringToMessageData(v___x_1926_);
return v___x_1927_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1930_ = l_Lean_stringToMessageData(v___x_1929_);
return v___x_1930_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1933_ = l_Lean_stringToMessageData(v___x_1932_);
return v___x_1933_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_1936_ = l_Lean_stringToMessageData(v___x_1935_);
return v___x_1936_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_1939_ = l_Lean_stringToMessageData(v___x_1938_);
return v___x_1939_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_1942_ = l_Lean_stringToMessageData(v___x_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1943_, lean_object* v_declHint_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v_env_1949_; uint8_t v___x_1950_; 
v___x_1947_ = lean_box(0);
v___x_1948_ = lean_st_ref_get(v___y_1945_);
v_env_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc_ref(v_env_1949_);
lean_dec(v___x_1948_);
v___x_1950_ = l_Lean_Name_isAnonymous(v_declHint_1944_);
if (v___x_1950_ == 0)
{
uint8_t v_isExporting_1951_; 
v_isExporting_1951_ = lean_ctor_get_uint8(v_env_1949_, sizeof(void*)*13);
if (v_isExporting_1951_ == 0)
{
lean_object* v___x_1952_; 
lean_dec_ref(v_env_1949_);
lean_dec(v_declHint_1944_);
v___x_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1952_, 0, v_msg_1943_);
return v___x_1952_;
}
else
{
lean_object* v___x_1953_; uint8_t v___x_1954_; 
lean_inc_ref(v_env_1949_);
v___x_1953_ = l_Lean_Environment_setExporting(v_env_1949_, v___x_1950_);
lean_inc(v_declHint_1944_);
lean_inc_ref(v___x_1953_);
v___x_1954_ = l_Lean_Environment_contains(v___x_1953_, v_declHint_1944_, v_isExporting_1951_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1955_; 
lean_dec_ref(v___x_1953_);
lean_dec_ref(v_env_1949_);
lean_dec(v_declHint_1944_);
v___x_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1955_, 0, v_msg_1943_);
return v___x_1955_;
}
else
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v_c_1961_; lean_object* v___x_1962_; 
v___x_1956_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_1957_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1958_ = l_Lean_Options_empty;
v___x_1959_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1953_);
lean_ctor_set(v___x_1959_, 1, v___x_1956_);
lean_ctor_set(v___x_1959_, 2, v___x_1957_);
lean_ctor_set(v___x_1959_, 3, v___x_1958_);
lean_inc(v_declHint_1944_);
v___x_1960_ = l_Lean_MessageData_ofConstName(v_declHint_1944_, v___x_1950_);
v_c_1961_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1961_, 0, v___x_1959_);
lean_ctor_set(v_c_1961_, 1, v___x_1960_);
v___x_1962_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1949_, v_declHint_1944_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_dec_ref(v_env_1949_);
lean_dec(v_declHint_1944_);
v___x_1963_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
lean_ctor_set(v___x_1964_, 1, v_c_1961_);
v___x_1965_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1964_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v___x_1967_ = l_Lean_MessageData_note(v___x_1966_);
v___x_1968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1968_, 0, v_msg_1943_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
v___x_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
return v___x_1969_;
}
else
{
lean_object* v_val_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2004_; 
v_val_1970_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1972_ = v___x_1962_;
v_isShared_1973_ = v_isSharedCheck_2004_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_val_1970_);
lean_dec(v___x_1962_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2004_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v_mod_1976_; uint8_t v___x_1977_; 
v___x_1974_ = l_Lean_Environment_header(v_env_1949_);
lean_dec_ref(v_env_1949_);
v___x_1975_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1974_);
v_mod_1976_ = lean_array_get(v___x_1947_, v___x_1975_, v_val_1970_);
lean_dec(v_val_1970_);
lean_dec_ref(v___x_1975_);
v___x_1977_ = l_Lean_isPrivateName(v_declHint_1944_);
lean_dec(v_declHint_1944_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1989_; 
v___x_1978_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
lean_ctor_set(v___x_1979_, 1, v_c_1961_);
v___x_1980_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1979_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
v___x_1982_ = l_Lean_MessageData_ofName(v_mod_1976_);
v___x_1983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1981_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
v___x_1984_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_1985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1983_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
v___x_1986_ = l_Lean_MessageData_note(v___x_1985_);
v___x_1987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1987_, 0, v_msg_1943_);
lean_ctor_set(v___x_1987_, 1, v___x_1986_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set_tag(v___x_1972_, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1987_);
v___x_1989_ = v___x_1972_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
else
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_1991_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
lean_ctor_set(v___x_1992_, 1, v_c_1961_);
v___x_1993_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_1994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1992_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = l_Lean_MessageData_ofName(v_mod_1976_);
v___x_1996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1994_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_1998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1996_);
lean_ctor_set(v___x_1998_, 1, v___x_1997_);
v___x_1999_ = l_Lean_MessageData_note(v___x_1998_);
v___x_2000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2000_, 0, v_msg_1943_);
lean_ctor_set(v___x_2000_, 1, v___x_1999_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set_tag(v___x_1972_, 0);
lean_ctor_set(v___x_1972_, 0, v___x_2000_);
v___x_2002_ = v___x_1972_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2005_; 
lean_dec_ref(v_env_1949_);
lean_dec(v_declHint_1944_);
v___x_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2005_, 0, v_msg_1943_);
return v___x_2005_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_2006_, lean_object* v_declHint_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_2006_, v_declHint_2007_, v___y_2008_);
lean_dec(v___y_2008_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_2011_, lean_object* v_declHint_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v___x_2018_; lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2028_; 
v___x_2018_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_2011_, v_declHint_2012_, v___y_2016_);
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2021_ = v___x_2018_;
v_isShared_2022_ = v_isSharedCheck_2028_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2018_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2028_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2023_ = l_Lean_unknownIdentifierMessageTag;
v___x_2024_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2023_);
lean_ctor_set(v___x_2024_, 1, v_a_2019_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2024_);
v___x_2026_ = v___x_2021_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_2029_, lean_object* v_declHint_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2029_, v_declHint_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object* v_msgData_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v___x_2043_; lean_object* v_env_2044_; uint8_t v___x_2045_; lean_object* v_env_2046_; lean_object* v___x_2047_; lean_object* v_toCold_2048_; lean_object* v_mctx_2049_; lean_object* v_lctx_2050_; lean_object* v_options_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2043_ = lean_st_ref_get(v___y_2041_);
v_env_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc_ref(v_env_2044_);
lean_dec(v___x_2043_);
v___x_2045_ = 0;
v_env_2046_ = l_Lean_Environment_setRecordingDeps(v_env_2044_, v___x_2045_);
v___x_2047_ = lean_st_ref_get(v___y_2039_);
v_toCold_2048_ = lean_ctor_get(v___y_2040_, 0);
v_mctx_2049_ = lean_ctor_get(v___x_2047_, 0);
lean_inc_ref(v_mctx_2049_);
lean_dec(v___x_2047_);
v_lctx_2050_ = lean_ctor_get(v___y_2038_, 2);
v_options_2051_ = lean_ctor_get(v_toCold_2048_, 2);
lean_inc_ref(v_options_2051_);
lean_inc_ref(v_lctx_2050_);
v___x_2052_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2052_, 0, v_env_2046_);
lean_ctor_set(v___x_2052_, 1, v_mctx_2049_);
lean_ctor_set(v___x_2052_, 2, v_lctx_2050_);
lean_ctor_set(v___x_2052_, 3, v_options_2051_);
v___x_2053_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
lean_ctor_set(v___x_2053_, 1, v_msgData_2037_);
v___x_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_ref_2068_; lean_object* v___x_2069_; lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2078_; 
v_ref_2068_ = lean_ctor_get(v___y_2065_, 2);
v___x_2069_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2072_ = v___x_2069_;
v_isShared_2073_ = v_isSharedCheck_2078_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2069_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2078_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; lean_object* v___x_2076_; 
lean_inc(v_ref_2068_);
v___x_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2074_, 0, v_ref_2068_);
lean_ctor_set(v___x_2074_, 1, v_a_2070_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set_tag(v___x_2072_, 1);
lean_ctor_set(v___x_2072_, 0, v___x_2074_);
v___x_2076_ = v___x_2072_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_2086_, lean_object* v_msg_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v_toCold_2093_; lean_object* v_currRecDepth_2094_; lean_object* v_ref_2095_; uint16_t v_optionFlags_2096_; uint8_t v_suppressElabErrors_2097_; uint8_t v_isRecordingDeps_2098_; lean_object* v_ref_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v_toCold_2093_ = lean_ctor_get(v___y_2090_, 0);
v_currRecDepth_2094_ = lean_ctor_get(v___y_2090_, 1);
v_ref_2095_ = lean_ctor_get(v___y_2090_, 2);
v_optionFlags_2096_ = lean_ctor_get_uint16(v___y_2090_, sizeof(void*)*3);
v_suppressElabErrors_2097_ = lean_ctor_get_uint8(v___y_2090_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2098_ = lean_ctor_get_uint8(v___y_2090_, sizeof(void*)*3 + 3);
v_ref_2099_ = l_Lean_replaceRef(v_ref_2086_, v_ref_2095_);
lean_inc(v_currRecDepth_2094_);
lean_inc_ref(v_toCold_2093_);
v___x_2100_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2100_, 0, v_toCold_2093_);
lean_ctor_set(v___x_2100_, 1, v_currRecDepth_2094_);
lean_ctor_set(v___x_2100_, 2, v_ref_2099_);
lean_ctor_set_uint16(v___x_2100_, sizeof(void*)*3, v_optionFlags_2096_);
lean_ctor_set_uint8(v___x_2100_, sizeof(void*)*3 + 2, v_suppressElabErrors_2097_);
lean_ctor_set_uint8(v___x_2100_, sizeof(void*)*3 + 3, v_isRecordingDeps_2098_);
v___x_2101_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_2087_, v___y_2088_, v___y_2089_, v___x_2100_, v___y_2091_);
lean_dec_ref_known(v___x_2100_, 3);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_2102_, lean_object* v_msg_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_2102_, v_msg_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v_ref_2102_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_2110_, lean_object* v_msg_2111_, lean_object* v_declHint_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v___x_2118_; lean_object* v_a_2119_; lean_object* v___x_2120_; 
v___x_2118_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2111_, v_declHint_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref(v___x_2118_);
v___x_2120_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_2110_, v_a_2119_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_2121_, lean_object* v_msg_2122_, lean_object* v_declHint_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_2121_, v_msg_2122_, v_declHint_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v_ref_2121_);
return v_res_2129_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_2132_ = l_Lean_stringToMessageData(v___x_2131_);
return v___x_2132_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2));
v___x_2135_ = l_Lean_stringToMessageData(v___x_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_2136_, lean_object* v_constName_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v___x_2143_; uint8_t v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2143_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_2144_ = 0;
lean_inc(v_constName_2137_);
v___x_2145_ = l_Lean_MessageData_ofConstName(v_constName_2137_, v___x_2144_);
v___x_2146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2143_);
lean_ctor_set(v___x_2146_, 1, v___x_2145_);
v___x_2147_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_2148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2146_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
v___x_2149_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_2136_, v___x_2148_, v_constName_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_2150_, lean_object* v_constName_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2150_, v_constName_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v_ref_2150_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_ref_2164_; lean_object* v___x_2165_; 
v_ref_2164_ = lean_ctor_get(v___y_2161_, 2);
v___x_2165_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2164_, v_constName_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(lean_object* v_constName_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v___x_2179_; lean_object* v_env_2180_; uint8_t v___x_2181_; lean_object* v___x_2182_; 
v___x_2179_ = lean_st_ref_get(v___y_2177_);
v_env_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc_ref(v_env_2180_);
lean_dec(v___x_2179_);
v___x_2181_ = 0;
lean_inc(v_constName_2173_);
v___x_2182_ = l_Lean_Environment_find_x3f(v_env_2180_, v_constName_2173_, v___x_2181_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
return v___x_2183_;
}
else
{
lean_object* v_val_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec(v_constName_2173_);
v_val_2184_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2182_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_val_2184_);
lean_dec(v___x_2182_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
lean_ctor_set_tag(v___x_2186_, 0);
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_val_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0___boxed(lean_object* v_constName_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(v_constName_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(lean_object* v_declName_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = lean_box(0);
lean_inc(v_declName_2199_);
v___x_2206_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(v_declName_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2232_; 
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2232_ == 0)
{
lean_object* v_unused_2233_; 
v_unused_2233_ = lean_ctor_get(v___x_2206_, 0);
lean_dec(v_unused_2233_);
v___x_2208_ = v___x_2206_;
v_isShared_2209_ = v_isSharedCheck_2232_;
goto v_resetjp_2207_;
}
else
{
lean_dec(v___x_2206_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2232_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v_env_2211_; lean_object* v___x_2212_; 
v___x_2210_ = lean_st_ref_get(v___y_2203_);
v_env_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc_ref(v_env_2211_);
lean_dec(v___x_2210_);
v___x_2212_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2211_, v_declName_2199_);
lean_dec(v_declName_2199_);
lean_dec_ref(v_env_2211_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2213_ = lean_box(0);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2213_);
v___x_2215_ = v___x_2208_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
else
{
lean_object* v_val_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2231_; 
v_val_2217_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2219_ = v___x_2212_;
v_isShared_2220_ = v_isSharedCheck_2231_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_val_2217_);
lean_dec(v___x_2212_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2231_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2221_; lean_object* v_env_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2221_ = lean_st_ref_get(v___y_2203_);
v_env_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc_ref(v_env_2222_);
lean_dec(v___x_2221_);
v___x_2223_ = l_Lean_Environment_allImportedModuleNames(v_env_2222_);
lean_dec_ref(v_env_2222_);
v___x_2224_ = lean_array_get(v___x_2205_, v___x_2223_, v_val_2217_);
lean_dec(v_val_2217_);
lean_dec_ref(v___x_2223_);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 0, v___x_2224_);
v___x_2226_ = v___x_2219_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
lean_object* v___x_2228_; 
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2226_);
v___x_2228_ = v___x_2208_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_dec(v_declName_2199_);
v_a_2234_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2206_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2206_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0___boxed(lean_object* v_declName_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(v_declName_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(lean_object* v_decl_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(v_decl_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2288_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2264_ = v___x_2261_;
v_isShared_2265_ = v_isSharedCheck_2288_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2261_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2288_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
if (lean_obj_tag(v_a_2262_) == 1)
{
lean_object* v_val_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2283_; 
v_val_2266_ = lean_ctor_get(v_a_2262_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v_a_2262_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2268_ = v_a_2262_;
v_isShared_2269_ = v_isSharedCheck_2283_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_val_2266_);
lean_dec(v_a_2262_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2283_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; uint8_t v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2278_; 
v___x_2270_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__1));
v___x_2271_ = 1;
v___x_2272_ = l_Lean_Name_toString(v_val_2266_, v___x_2271_);
v___x_2273_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
v___x_2274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2270_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
v___x_2275_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__3));
v___x_2276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2274_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 0, v___x_2276_);
v___x_2278_ = v___x_2268_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
lean_object* v___x_2280_; 
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v___x_2278_);
v___x_2280_ = v___x_2264_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2278_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
else
{
lean_object* v___x_2284_; lean_object* v___x_2286_; 
lean_dec(v_a_2262_);
v___x_2284_ = lean_box(0);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v___x_2284_);
v___x_2286_ = v___x_2264_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
v_a_2289_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2261_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2261_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___boxed(lean_object* v_decl_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(v_decl_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
lean_dec(v_a_2301_);
lean_dec_ref(v_a_2300_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2304_, lean_object* v_constName_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2312_, lean_object* v_constName_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1(v_00_u03b1_2312_, v_constName_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2320_, lean_object* v_ref_2321_, lean_object* v_constName_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2321_, v_constName_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2329_, lean_object* v_ref_2330_, lean_object* v_constName_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2329_, v_ref_2330_, v_constName_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v_ref_2330_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_2338_, lean_object* v_ref_2339_, lean_object* v_msg_2340_, lean_object* v_declHint_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_2339_, v_msg_2340_, v_declHint_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2348_, lean_object* v_ref_2349_, lean_object* v_msg_2350_, lean_object* v_declHint_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_00_u03b1_2348_, v_ref_2349_, v_msg_2350_, v_declHint_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v_ref_2349_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_2358_, lean_object* v_declHint_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v___x_2365_; 
v___x_2365_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_2358_, v_declHint_2359_, v___y_2363_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2366_, lean_object* v_declHint_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_2366_, v_declHint_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_2374_, lean_object* v_ref_2375_, lean_object* v_msg_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_2375_, v_msg_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2383_, lean_object* v_ref_2384_, lean_object* v_msg_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_2383_, v_ref_2384_, v_msg_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v_ref_2384_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_2392_, lean_object* v_msg_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2400_, lean_object* v_msg_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_2400_, v_msg_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
return v_res_2407_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(lean_object* v_a_2408_){
_start:
{
switch(lean_obj_tag(v_a_2408_))
{
case 3:
{
uint8_t v___x_2409_; 
v___x_2409_ = 1;
return v___x_2409_;
}
case 6:
{
lean_object* v_a_2410_; 
v_a_2410_ = lean_ctor_get(v_a_2408_, 0);
v_a_2408_ = v_a_2410_;
goto _start;
}
case 4:
{
lean_object* v_f_2412_; 
v_f_2412_ = lean_ctor_get(v_a_2408_, 1);
v_a_2408_ = v_f_2412_;
goto _start;
}
case 7:
{
lean_object* v_a_2414_; 
v_a_2414_ = lean_ctor_get(v_a_2408_, 1);
v_a_2408_ = v_a_2414_;
goto _start;
}
default: 
{
uint8_t v___x_2416_; 
v___x_2416_ = 0;
return v___x_2416_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat___boxed(lean_object* v_a_2417_){
_start:
{
uint8_t v_res_2418_; lean_object* v_r_2419_; 
v_res_2418_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(v_a_2417_);
lean_dec(v_a_2417_);
v_r_2419_ = lean_box(v_res_2418_);
return v_r_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(lean_object* v_e_2420_, lean_object* v___y_2421_){
_start:
{
uint8_t v___x_2423_; 
v___x_2423_ = l_Lean_Expr_hasMVar(v_e_2420_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2424_; 
v___x_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2424_, 0, v_e_2420_);
return v___x_2424_;
}
else
{
lean_object* v___x_2425_; lean_object* v_mctx_2426_; lean_object* v___x_2427_; lean_object* v_fst_2428_; lean_object* v_snd_2429_; lean_object* v___x_2430_; lean_object* v_cache_2431_; lean_object* v_zetaDeltaFVarIds_2432_; lean_object* v_postponed_2433_; lean_object* v_diag_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2443_; 
v___x_2425_ = lean_st_ref_get(v___y_2421_);
v_mctx_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc_ref(v_mctx_2426_);
lean_dec(v___x_2425_);
v___x_2427_ = l_Lean_instantiateMVarsCore(v_mctx_2426_, v_e_2420_);
v_fst_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_fst_2428_);
v_snd_2429_ = lean_ctor_get(v___x_2427_, 1);
lean_inc(v_snd_2429_);
lean_dec_ref(v___x_2427_);
v___x_2430_ = lean_st_ref_take(v___y_2421_);
v_cache_2431_ = lean_ctor_get(v___x_2430_, 1);
v_zetaDeltaFVarIds_2432_ = lean_ctor_get(v___x_2430_, 2);
v_postponed_2433_ = lean_ctor_get(v___x_2430_, 3);
v_diag_2434_ = lean_ctor_get(v___x_2430_, 4);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2443_ == 0)
{
lean_object* v_unused_2444_; 
v_unused_2444_ = lean_ctor_get(v___x_2430_, 0);
lean_dec(v_unused_2444_);
v___x_2436_ = v___x_2430_;
v_isShared_2437_ = v_isSharedCheck_2443_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_diag_2434_);
lean_inc(v_postponed_2433_);
lean_inc(v_zetaDeltaFVarIds_2432_);
lean_inc(v_cache_2431_);
lean_dec(v___x_2430_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2443_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v_snd_2429_);
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_snd_2429_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v_cache_2431_);
lean_ctor_set(v_reuseFailAlloc_2442_, 2, v_zetaDeltaFVarIds_2432_);
lean_ctor_set(v_reuseFailAlloc_2442_, 3, v_postponed_2433_);
lean_ctor_set(v_reuseFailAlloc_2442_, 4, v_diag_2434_);
v___x_2439_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2440_ = lean_st_ref_put(v___y_2421_, v___x_2439_);
v___x_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2441_, 0, v_fst_2428_);
return v___x_2441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg___boxed(lean_object* v_e_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_e_2445_, v___y_2446_);
lean_dec(v___y_2446_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0(lean_object* v_e_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v___x_2455_; 
v___x_2455_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_e_2449_, v___y_2451_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___boxed(lean_object* v_e_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0(v_e_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(lean_object* v_i_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_){
_start:
{
switch(lean_obj_tag(v_i_2474_))
{
case 1:
{
lean_object* v_i_2480_; lean_object* v_expr_2481_; uint8_t v_isDisplayableTerm_2482_; lean_object* v___x_2483_; lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2604_; 
v_i_2480_ = lean_ctor_get(v_i_2474_, 0);
lean_inc_ref(v_i_2480_);
lean_dec_ref_known(v_i_2474_, 1);
v_expr_2481_ = lean_ctor_get(v_i_2480_, 3);
lean_inc_ref(v_expr_2481_);
v_isDisplayableTerm_2482_ = lean_ctor_get_uint8(v_i_2480_, sizeof(void*)*4 + 1);
lean_dec_ref(v_i_2480_);
v___x_2483_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_expr_2481_, v_a_2476_);
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2604_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2604_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
uint8_t v___x_2488_; 
v___x_2488_ = l_Lean_Expr_isSort(v_a_2484_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2489_; 
lean_del_object(v___x_2486_);
lean_inc(v_a_2478_);
lean_inc_ref(v_a_2477_);
lean_inc(v_a_2476_);
lean_inc_ref(v_a_2475_);
lean_inc(v_a_2484_);
v___x_2489_ = lean_infer_type(v_a_2484_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; lean_object* v___x_2491_; lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2591_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2490_);
lean_dec_ref_known(v___x_2489_, 1);
v___x_2491_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_a_2490_, v_a_2476_);
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2494_ = v___x_2491_;
v_isShared_2495_ = v_isSharedCheck_2591_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2491_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2591_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2496_; 
v___x_2496_ = l_Lean_Meta_ppExpr(v_a_2492_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_);
if (lean_obj_tag(v___x_2496_) == 0)
{
if (lean_obj_tag(v_a_2484_) == 4)
{
lean_object* v_declName_2497_; lean_object* v___x_2498_; 
lean_dec_ref_known(v___x_2496_, 1);
v_declName_2497_ = lean_ctor_get(v_a_2484_, 0);
lean_inc_n(v_declName_2497_, 2);
lean_dec_ref_known(v_a_2484_, 2);
v___x_2498_ = l_Lean_PrettyPrinter_ppSignature(v_declName_2497_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; lean_object* v___x_2500_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_a_2499_);
lean_dec_ref_known(v___x_2498_, 1);
v___x_2500_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(v_declName_2497_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2525_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2503_ = v___x_2500_;
v_isShared_2504_ = v_isSharedCheck_2525_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2500_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2525_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v_fmt_2505_; lean_object* v_infos_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2524_; 
v_fmt_2505_ = lean_ctor_get(v_a_2499_, 0);
v_infos_2506_ = lean_ctor_get(v_a_2499_, 1);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_a_2499_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2508_ = v_a_2499_;
v_isShared_2509_ = v_isSharedCheck_2524_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_infos_2506_);
lean_inc(v_fmt_2505_);
lean_dec(v_a_2499_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2524_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2515_; 
v___x_2510_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1));
v___x_2511_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
lean_ctor_set(v___x_2511_, 1, v_fmt_2505_);
v___x_2512_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3));
v___x_2513_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2511_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 0, v___x_2513_);
v___x_2515_ = v___x_2508_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2513_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v_infos_2506_);
v___x_2515_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
lean_object* v___x_2517_; 
if (v_isShared_2495_ == 0)
{
lean_ctor_set_tag(v___x_2494_, 1);
lean_ctor_set(v___x_2494_, 0, v___x_2515_);
v___x_2517_ = v___x_2494_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
lean_object* v___x_2518_; lean_object* v___x_2520_; 
v___x_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2517_);
lean_ctor_set(v___x_2518_, 1, v_a_2501_);
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 0, v___x_2518_);
v___x_2520_ = v___x_2503_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec(v_a_2499_);
lean_del_object(v___x_2494_);
v_a_2526_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2500_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2500_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_dec(v_declName_2497_);
lean_del_object(v___x_2494_);
v_a_2534_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2498_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2498_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2543_; 
v_a_2542_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2542_);
lean_dec_ref_known(v___x_2496_, 1);
lean_inc(v_a_2484_);
v___x_2543_ = l_Lean_Meta_ppExpr(v_a_2484_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2574_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2546_ = v___x_2543_;
v_isShared_2547_ = v_isSharedCheck_2574_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2543_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2574_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___y_2549_; 
if (v_isDisplayableTerm_2482_ == 0)
{
if (lean_obj_tag(v_a_2484_) == 1)
{
lean_object* v_lctx_2568_; lean_object* v___x_2569_; 
v_lctx_2568_ = lean_ctor_get(v_a_2475_, 2);
lean_inc_ref(v_lctx_2568_);
v___x_2569_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_2568_, v_a_2484_);
lean_dec_ref_known(v_a_2484_, 1);
if (lean_obj_tag(v___x_2569_) == 1)
{
lean_object* v_val_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; 
v_val_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_val_2570_);
lean_dec_ref_known(v___x_2569_, 1);
v___x_2571_ = l_Lean_LocalDecl_userName(v_val_2570_);
lean_dec(v_val_2570_);
v___x_2572_ = l_Lean_Name_hasMacroScopes(v___x_2571_);
lean_dec(v___x_2571_);
if (v___x_2572_ == 0)
{
goto v___jp_2564_;
}
else
{
lean_dec(v_a_2544_);
v___y_2549_ = v_a_2542_;
goto v___jp_2548_;
}
}
else
{
lean_dec(v___x_2569_);
lean_dec(v_a_2544_);
v___y_2549_ = v_a_2542_;
goto v___jp_2548_;
}
}
else
{
uint8_t v___x_2573_; 
lean_dec(v_a_2484_);
v___x_2573_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(v_a_2544_);
if (v___x_2573_ == 0)
{
lean_dec(v_a_2544_);
v___y_2549_ = v_a_2542_;
goto v___jp_2548_;
}
else
{
goto v___jp_2564_;
}
}
}
else
{
lean_dec(v_a_2484_);
goto v___jp_2564_;
}
v___jp_2548_:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2557_; 
v___x_2550_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1));
v___x_2551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
lean_ctor_set(v___x_2551_, 1, v___y_2549_);
v___x_2552_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3));
v___x_2553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2551_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = lean_box(1);
v___x_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2553_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set_tag(v___x_2494_, 1);
lean_ctor_set(v___x_2494_, 0, v___x_2555_);
v___x_2557_ = v___x_2494_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2555_);
v___x_2557_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2561_; 
v___x_2558_ = lean_box(0);
v___x_2559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2557_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 0, v___x_2559_);
v___x_2561_ = v___x_2546_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2559_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
v___jp_2564_:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2565_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5));
v___x_2566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2566_, 0, v_a_2544_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
lean_ctor_set(v___x_2567_, 1, v_a_2542_);
v___y_2549_ = v___x_2567_;
goto v___jp_2548_;
}
}
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
lean_dec(v_a_2542_);
lean_del_object(v___x_2494_);
lean_dec(v_a_2484_);
v_a_2575_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2543_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2543_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
lean_del_object(v___x_2494_);
lean_dec(v_a_2484_);
v_a_2583_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2496_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2496_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v_a_2484_);
v_a_2592_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2489_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2489_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_object* v___x_2600_; lean_object* v___x_2602_; 
lean_dec(v_a_2484_);
v___x_2600_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6));
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 0, v___x_2600_);
v___x_2602_ = v___x_2486_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
case 7:
{
lean_object* v_i_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2655_; 
v_i_2605_ = lean_ctor_get(v_i_2474_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v_i_2474_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2607_ = v_i_2474_;
v_isShared_2608_ = v_isSharedCheck_2655_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_i_2605_);
lean_dec(v_i_2474_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2655_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v_fieldName_2609_; lean_object* v_val_2610_; lean_object* v___x_2611_; 
v_fieldName_2609_ = lean_ctor_get(v_i_2605_, 1);
lean_inc(v_fieldName_2609_);
v_val_2610_ = lean_ctor_get(v_i_2605_, 3);
lean_inc_ref(v_val_2610_);
lean_dec_ref(v_i_2605_);
lean_inc(v_a_2478_);
lean_inc_ref(v_a_2477_);
lean_inc(v_a_2476_);
lean_inc_ref(v_a_2475_);
v___x_2611_ = lean_infer_type(v_val_2610_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v___x_2613_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2611_, 1);
v___x_2613_ = l_Lean_Meta_ppExpr(v_a_2612_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2638_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2616_ = v___x_2613_;
v_isShared_2617_ = v_isSharedCheck_2638_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2638_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2618_; uint8_t v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2622_; 
v___x_2618_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1));
v___x_2619_ = 1;
v___x_2620_ = l_Lean_Name_toString(v_fieldName_2609_, v___x_2619_);
if (v_isShared_2608_ == 0)
{
lean_ctor_set_tag(v___x_2607_, 3);
lean_ctor_set(v___x_2607_, 0, v___x_2620_);
v___x_2622_ = v___x_2607_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2635_; 
v___x_2623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2618_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
v___x_2624_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5));
v___x_2625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2623_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
v___x_2626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
lean_ctor_set(v___x_2626_, 1, v_a_2614_);
v___x_2627_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3));
v___x_2628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2626_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
v___x_2629_ = lean_box(1);
v___x_2630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2628_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
v___x_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2630_);
v___x_2632_ = lean_box(0);
v___x_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2631_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2633_);
v___x_2635_ = v___x_2616_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_dec(v_fieldName_2609_);
lean_del_object(v___x_2607_);
v_a_2639_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2613_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2613_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_dec(v_fieldName_2609_);
lean_del_object(v___x_2607_);
v_a_2647_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2611_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2611_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
}
default: 
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
lean_dec_ref(v_i_2474_);
v___x_2656_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6));
v___x_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2656_);
return v___x_2657_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___boxed(lean_object* v_i_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(v_i_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__0(lean_object* v_snd_2665_, lean_object* v_____r_2666_, lean_object* v_fmts_2667_, lean_object* v_infos_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2674_, 0, v_fmts_2667_);
lean_ctor_set(v___x_2674_, 1, v_infos_2668_);
v___x_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2675_, 0, v_snd_2665_);
lean_ctor_set(v___x_2675_, 1, v___x_2674_);
v___x_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2675_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__0___boxed(lean_object* v_snd_2677_, lean_object* v_____r_2678_, lean_object* v_fmts_2679_, lean_object* v_infos_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(v_snd_2677_, v_____r_2678_, v_fmts_2679_, v_infos_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0_spec__0(lean_object* v_x_2687_, lean_object* v_x_2688_, lean_object* v_x_2689_){
_start:
{
if (lean_obj_tag(v_x_2689_) == 0)
{
lean_dec(v_x_2687_);
return v_x_2688_;
}
else
{
lean_object* v_head_2690_; lean_object* v_tail_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2700_; 
v_head_2690_ = lean_ctor_get(v_x_2689_, 0);
v_tail_2691_ = lean_ctor_get(v_x_2689_, 1);
v_isSharedCheck_2700_ = !lean_is_exclusive(v_x_2689_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2693_ = v_x_2689_;
v_isShared_2694_ = v_isSharedCheck_2700_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_tail_2691_);
lean_inc(v_head_2690_);
lean_dec(v_x_2689_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2700_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
lean_inc(v_x_2687_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set_tag(v___x_2693_, 5);
lean_ctor_set(v___x_2693_, 1, v_x_2687_);
lean_ctor_set(v___x_2693_, 0, v_x_2688_);
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_x_2688_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_x_2687_);
v___x_2696_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v___x_2697_; 
v___x_2697_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2696_);
lean_ctor_set(v___x_2697_, 1, v_head_2690_);
v_x_2688_ = v___x_2697_;
v_x_2689_ = v_tail_2691_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0(lean_object* v_x_2701_, lean_object* v_x_2702_){
_start:
{
if (lean_obj_tag(v_x_2701_) == 0)
{
lean_object* v___x_2703_; 
lean_dec(v_x_2702_);
v___x_2703_ = lean_box(0);
return v___x_2703_;
}
else
{
lean_object* v_tail_2704_; 
v_tail_2704_ = lean_ctor_get(v_x_2701_, 1);
if (lean_obj_tag(v_tail_2704_) == 0)
{
lean_object* v_head_2705_; 
lean_dec(v_x_2702_);
v_head_2705_ = lean_ctor_get(v_x_2701_, 0);
lean_inc(v_head_2705_);
lean_dec_ref_known(v_x_2701_, 2);
return v_head_2705_;
}
else
{
lean_object* v_head_2706_; lean_object* v___x_2707_; 
lean_inc(v_tail_2704_);
v_head_2706_ = lean_ctor_get(v_x_2701_, 0);
lean_inc(v_head_2706_);
lean_dec_ref_known(v_x_2701_, 2);
v___x_2707_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0_spec__0(v_x_2702_, v_head_2706_, v_tail_2704_);
return v___x_2707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__1(lean_object* v___x_2711_, lean_object* v_i_2712_, lean_object* v_fmts_2713_, lean_object* v_infos_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v___y_2721_; lean_object* v_fmts_2722_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v_fmts_2736_; lean_object* v_fst_2740_; lean_object* v_fst_2741_; lean_object* v_snd_2742_; lean_object* v___y_2763_; uint8_t v___y_2764_; lean_object* v_a_2768_; lean_object* v___y_2772_; lean_object* v___x_2778_; 
lean_inc_ref(v_i_2712_);
v___x_2778_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(v_i_2712_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v_fst_2780_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref_known(v___x_2778_, 1);
v_fst_2780_ = lean_ctor_get(v_a_2779_, 0);
if (lean_obj_tag(v_fst_2780_) == 1)
{
lean_object* v_val_2781_; lean_object* v_snd_2782_; lean_object* v_fmt_2783_; lean_object* v_infos_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
lean_dec(v_infos_2714_);
v_val_2781_ = lean_ctor_get(v_fst_2780_, 0);
lean_inc(v_val_2781_);
v_snd_2782_ = lean_ctor_get(v_a_2779_, 1);
lean_inc(v_snd_2782_);
lean_dec(v_a_2779_);
v_fmt_2783_ = lean_ctor_get(v_val_2781_, 0);
lean_inc(v_fmt_2783_);
v_infos_2784_ = lean_ctor_get(v_val_2781_, 1);
lean_inc(v_infos_2784_);
lean_dec(v_val_2781_);
v___x_2785_ = lean_array_push(v_fmts_2713_, v_fmt_2783_);
v___x_2786_ = lean_box(0);
v___x_2787_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(v_snd_2782_, v___x_2786_, v___x_2785_, v_infos_2784_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
v___y_2772_ = v___x_2787_;
goto v___jp_2771_;
}
else
{
lean_object* v_snd_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v_snd_2788_ = lean_ctor_get(v_a_2779_, 1);
lean_inc(v_snd_2788_);
lean_dec(v_a_2779_);
v___x_2789_ = lean_box(0);
v___x_2790_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(v_snd_2788_, v___x_2789_, v_fmts_2713_, v_infos_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
v___y_2772_ = v___x_2790_;
goto v___jp_2771_;
}
}
else
{
lean_object* v_a_2791_; 
v_a_2791_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2791_);
lean_dec_ref_known(v___x_2778_, 1);
v_a_2768_ = v_a_2791_;
goto v___jp_2767_;
}
v___jp_2720_:
{
lean_object* v___x_2723_; uint8_t v___x_2724_; 
v___x_2723_ = lean_array_get_size(v_fmts_2722_);
v___x_2724_ = lean_nat_dec_eq(v___x_2723_, v___x_2711_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2725_ = lean_array_to_list(v_fmts_2722_);
v___x_2726_ = ((lean_object*)(l_Lean_Elab_Info_fmtHover_x3f___lam__1___closed__1));
v___x_2727_ = l_Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0(v___x_2725_, v___x_2726_);
v___x_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2727_);
lean_ctor_set(v___x_2728_, 1, v___y_2721_);
v___x_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
v___x_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2729_);
return v___x_2730_;
}
else
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
lean_dec_ref(v_fmts_2722_);
lean_dec(v___y_2721_);
v___x_2731_ = lean_box(0);
v___x_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2731_);
return v___x_2732_;
}
}
v___jp_2733_:
{
if (lean_obj_tag(v___y_2735_) == 1)
{
lean_object* v_val_2737_; lean_object* v___x_2738_; 
v_val_2737_ = lean_ctor_get(v___y_2735_, 0);
lean_inc(v_val_2737_);
lean_dec_ref_known(v___y_2735_, 1);
v___x_2738_ = lean_array_push(v_fmts_2736_, v_val_2737_);
v___y_2721_ = v___y_2734_;
v_fmts_2722_ = v___x_2738_;
goto v___jp_2720_;
}
else
{
lean_dec(v___y_2735_);
v___y_2721_ = v___y_2734_;
v_fmts_2722_ = v_fmts_2736_;
goto v___jp_2720_;
}
}
v___jp_2739_:
{
lean_object* v___x_2743_; 
v___x_2743_ = l_Lean_Elab_Info_docString_x3f(v_i_2712_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; 
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_a_2744_);
lean_dec_ref_known(v___x_2743_, 1);
if (lean_obj_tag(v_a_2744_) == 1)
{
lean_object* v_val_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2753_; 
v_val_2745_ = lean_ctor_get(v_a_2744_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v_a_2744_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2747_ = v_a_2744_;
v_isShared_2748_ = v_isSharedCheck_2753_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_val_2745_);
lean_dec(v_a_2744_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2753_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
lean_ctor_set_tag(v___x_2747_, 3);
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_val_2745_);
v___x_2750_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
lean_object* v___x_2751_; 
v___x_2751_ = lean_array_push(v_fst_2741_, v___x_2750_);
v___y_2734_ = v_snd_2742_;
v___y_2735_ = v_fst_2740_;
v_fmts_2736_ = v___x_2751_;
goto v___jp_2733_;
}
}
}
else
{
lean_dec(v_a_2744_);
v___y_2734_ = v_snd_2742_;
v___y_2735_ = v_fst_2740_;
v_fmts_2736_ = v_fst_2741_;
goto v___jp_2733_;
}
}
else
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
lean_dec(v_snd_2742_);
lean_dec(v_fst_2741_);
lean_dec(v_fst_2740_);
v_a_2754_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2743_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2743_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
v___jp_2762_:
{
if (v___y_2764_ == 0)
{
lean_object* v___x_2765_; 
lean_dec_ref(v___y_2763_);
v___x_2765_ = lean_box(0);
v_fst_2740_ = v___x_2765_;
v_fst_2741_ = v_fmts_2713_;
v_snd_2742_ = v_infos_2714_;
goto v___jp_2739_;
}
else
{
lean_object* v___x_2766_; 
lean_dec(v_infos_2714_);
lean_dec_ref(v_fmts_2713_);
lean_dec_ref(v_i_2712_);
v___x_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2766_, 0, v___y_2763_);
return v___x_2766_;
}
}
v___jp_2767_:
{
uint8_t v___x_2769_; 
v___x_2769_ = l_Lean_Exception_isInterrupt(v_a_2768_);
if (v___x_2769_ == 0)
{
uint8_t v___x_2770_; 
lean_inc_ref(v_a_2768_);
v___x_2770_ = l_Lean_Exception_isRuntime(v_a_2768_);
v___y_2763_ = v_a_2768_;
v___y_2764_ = v___x_2770_;
goto v___jp_2762_;
}
else
{
v___y_2763_ = v_a_2768_;
v___y_2764_ = v___x_2769_;
goto v___jp_2762_;
}
}
v___jp_2771_:
{
lean_object* v_a_2773_; lean_object* v_snd_2774_; lean_object* v_fst_2775_; lean_object* v_fst_2776_; lean_object* v_snd_2777_; 
v_a_2773_ = lean_ctor_get(v___y_2772_, 0);
lean_inc(v_a_2773_);
lean_dec_ref(v___y_2772_);
v_snd_2774_ = lean_ctor_get(v_a_2773_, 1);
lean_inc(v_snd_2774_);
v_fst_2775_ = lean_ctor_get(v_a_2773_, 0);
lean_inc(v_fst_2775_);
lean_dec(v_a_2773_);
v_fst_2776_ = lean_ctor_get(v_snd_2774_, 0);
lean_inc(v_fst_2776_);
v_snd_2777_ = lean_ctor_get(v_snd_2774_, 1);
lean_inc(v_snd_2777_);
lean_dec(v_snd_2774_);
v_fst_2740_ = v_fst_2775_;
v_fst_2741_ = v_fst_2776_;
v_snd_2742_ = v_snd_2777_;
goto v___jp_2739_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__1___boxed(lean_object* v___x_2792_, lean_object* v_i_2793_, lean_object* v_fmts_2794_, lean_object* v_infos_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Lean_Elab_Info_fmtHover_x3f___lam__1(v___x_2792_, v_i_2793_, v_fmts_2794_, v_infos_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___x_2792_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f(lean_object* v_ci_2804_, lean_object* v_i_2805_){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v_fmts_2809_; lean_object* v_infos_2810_; lean_object* v___f_2811_; lean_object* v___x_2812_; 
v___x_2807_ = l_Lean_Elab_Info_lctx(v_i_2805_);
v___x_2808_ = lean_unsigned_to_nat(0u);
v_fmts_2809_ = ((lean_object*)(l_Lean_Elab_Info_fmtHover_x3f___closed__0));
v_infos_2810_ = lean_box(1);
v___f_2811_ = lean_alloc_closure((void*)(l_Lean_Elab_Info_fmtHover_x3f___lam__1___boxed), 9, 4);
lean_closure_set(v___f_2811_, 0, v___x_2808_);
lean_closure_set(v___f_2811_, 1, v_i_2805_);
lean_closure_set(v___f_2811_, 2, v_fmts_2809_);
lean_closure_set(v___f_2811_, 3, v_infos_2810_);
v___x_2812_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ci_2804_, v___x_2807_, v___f_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___boxed(lean_object* v_ci_2813_, lean_object* v_i_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Lean_Elab_Info_fmtHover_x3f(v_ci_2813_, v_i_2814_);
return v_res_2816_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(lean_object* v_hoverPos_2825_, lean_object* v_pos_2826_, lean_object* v_tailPos_2827_, lean_object* v_as_2828_, size_t v_i_2829_, size_t v_stop_2830_){
_start:
{
uint8_t v___x_2831_; 
v___x_2831_ = lean_usize_dec_eq(v_i_2829_, v_stop_2830_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2832_; uint8_t v___x_2833_; 
v___x_2832_ = lean_array_uget_borrowed(v_as_2828_, v_i_2829_);
v___x_2833_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(v_hoverPos_2825_, v_pos_2826_, v_tailPos_2827_, v___x_2832_);
if (v___x_2833_ == 0)
{
size_t v___x_2834_; size_t v___x_2835_; 
v___x_2834_ = ((size_t)1ULL);
v___x_2835_ = lean_usize_add(v_i_2829_, v___x_2834_);
v_i_2829_ = v___x_2835_;
goto _start;
}
else
{
return v___x_2833_;
}
}
else
{
uint8_t v___x_2837_; 
v___x_2837_ = 0;
return v___x_2837_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(lean_object* v_hoverPos_2838_, lean_object* v_pos_2839_, lean_object* v_tailPos_2840_, lean_object* v_x_2841_){
_start:
{
if (lean_obj_tag(v_x_2841_) == 0)
{
lean_object* v_cs_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; uint8_t v___x_2845_; 
v_cs_2842_ = lean_ctor_get(v_x_2841_, 0);
v___x_2843_ = lean_unsigned_to_nat(0u);
v___x_2844_ = lean_array_get_size(v_cs_2842_);
v___x_2845_ = lean_nat_dec_lt(v___x_2843_, v___x_2844_);
if (v___x_2845_ == 0)
{
return v___x_2845_;
}
else
{
if (v___x_2845_ == 0)
{
return v___x_2845_;
}
else
{
size_t v___x_2846_; size_t v___x_2847_; uint8_t v___x_2848_; 
v___x_2846_ = ((size_t)0ULL);
v___x_2847_ = lean_usize_of_nat(v___x_2844_);
v___x_2848_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(v_hoverPos_2838_, v_pos_2839_, v_tailPos_2840_, v_cs_2842_, v___x_2846_, v___x_2847_);
return v___x_2848_;
}
}
}
else
{
lean_object* v_vs_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; 
v_vs_2849_ = lean_ctor_get(v_x_2841_, 0);
v___x_2850_ = lean_unsigned_to_nat(0u);
v___x_2851_ = lean_array_get_size(v_vs_2849_);
v___x_2852_ = lean_nat_dec_lt(v___x_2850_, v___x_2851_);
if (v___x_2852_ == 0)
{
return v___x_2852_;
}
else
{
if (v___x_2852_ == 0)
{
return v___x_2852_;
}
else
{
size_t v___x_2853_; size_t v___x_2854_; uint8_t v___x_2855_; 
v___x_2853_ = ((size_t)0ULL);
v___x_2854_ = lean_usize_of_nat(v___x_2851_);
v___x_2855_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_2838_, v_pos_2839_, v_tailPos_2840_, v_vs_2849_, v___x_2853_, v___x_2854_);
return v___x_2855_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(lean_object* v_hoverPos_2856_, lean_object* v_pos_2857_, lean_object* v_tailPos_2858_, lean_object* v_t_2859_){
_start:
{
lean_object* v_root_2860_; lean_object* v_tail_2861_; uint8_t v___x_2862_; 
v_root_2860_ = lean_ctor_get(v_t_2859_, 0);
v_tail_2861_ = lean_ctor_get(v_t_2859_, 1);
v___x_2862_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(v_hoverPos_2856_, v_pos_2857_, v_tailPos_2858_, v_root_2860_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; 
v___x_2863_ = lean_unsigned_to_nat(0u);
v___x_2864_ = lean_array_get_size(v_tail_2861_);
v___x_2865_ = lean_nat_dec_lt(v___x_2863_, v___x_2864_);
if (v___x_2865_ == 0)
{
return v___x_2865_;
}
else
{
if (v___x_2865_ == 0)
{
return v___x_2865_;
}
else
{
size_t v___x_2866_; size_t v___x_2867_; uint8_t v___x_2868_; 
v___x_2866_ = ((size_t)0ULL);
v___x_2867_ = lean_usize_of_nat(v___x_2864_);
v___x_2868_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_2856_, v_pos_2857_, v_tailPos_2858_, v_tail_2861_, v___x_2866_, v___x_2867_);
return v___x_2868_;
}
}
}
else
{
return v___x_2862_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(lean_object* v_hoverPos_2869_, lean_object* v_pos_2870_, lean_object* v_tailPos_2871_, lean_object* v_a_2872_){
_start:
{
if (lean_obj_tag(v_a_2872_) == 1)
{
lean_object* v_i_2873_; 
v_i_2873_ = lean_ctor_get(v_a_2872_, 0);
switch(lean_obj_tag(v_i_2873_))
{
case 0:
{
lean_object* v_children_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
v_children_2874_ = lean_ctor_get(v_a_2872_, 1);
v___x_2875_ = l_Lean_Elab_Info_stx(v_i_2873_);
v___x_2876_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3));
v___x_2877_ = l_Lean_Syntax_isOfKind(v___x_2875_, v___x_2876_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; 
v___x_2878_ = l_Lean_Elab_Info_pos_x3f(v_i_2873_);
if (lean_obj_tag(v___x_2878_) == 1)
{
lean_object* v_val_2879_; lean_object* v___x_2880_; 
v_val_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_val_2879_);
lean_dec_ref_known(v___x_2878_, 1);
v___x_2880_ = l_Lean_Elab_Info_tailPos_x3f(v_i_2873_);
if (lean_obj_tag(v___x_2880_) == 1)
{
lean_object* v_val_2881_; uint8_t v___x_2882_; uint8_t v___y_2884_; lean_object* v___x_2886_; lean_object* v___x_2887_; uint8_t v___x_2888_; 
v_val_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_val_2881_);
lean_dec_ref_known(v___x_2880_, 1);
v___x_2882_ = 1;
v___x_2886_ = lean_unsigned_to_nat(1u);
v___x_2887_ = lean_nat_add(v_hoverPos_2869_, v___x_2886_);
v___x_2888_ = lean_nat_dec_le(v___x_2887_, v_val_2881_);
lean_dec(v___x_2887_);
if (v___x_2888_ == 0)
{
lean_dec(v_val_2881_);
lean_dec(v_val_2879_);
v___y_2884_ = v___x_2877_;
goto v___jp_2883_;
}
else
{
uint8_t v_decide_2889_; 
v_decide_2889_ = lean_nat_dec_eq(v_val_2879_, v_pos_2870_);
lean_dec(v_val_2879_);
if (v_decide_2889_ == 0)
{
lean_dec(v_val_2881_);
v___y_2884_ = v___x_2888_;
goto v___jp_2883_;
}
else
{
uint8_t v_decide_2890_; 
v_decide_2890_ = lean_nat_dec_eq(v_val_2881_, v_tailPos_2871_);
lean_dec(v_val_2881_);
if (v_decide_2890_ == 0)
{
v___y_2884_ = v___x_2888_;
goto v___jp_2883_;
}
else
{
v___y_2884_ = v___x_2877_;
goto v___jp_2883_;
}
}
}
v___jp_2883_:
{
if (v___y_2884_ == 0)
{
uint8_t v___x_2885_; 
v___x_2885_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2869_, v_pos_2870_, v_tailPos_2871_, v_children_2874_);
return v___x_2885_;
}
else
{
return v___x_2882_;
}
}
}
else
{
uint8_t v___x_2891_; 
lean_dec(v___x_2880_);
lean_dec(v_val_2879_);
v___x_2891_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2869_, v_pos_2870_, v_tailPos_2871_, v_children_2874_);
return v___x_2891_;
}
}
else
{
uint8_t v___x_2892_; 
lean_dec(v___x_2878_);
v___x_2892_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2869_, v_pos_2870_, v_tailPos_2871_, v_children_2874_);
return v___x_2892_;
}
}
else
{
uint8_t v___x_2893_; 
v___x_2893_ = 0;
return v___x_2893_;
}
}
case 4:
{
lean_object* v_children_2894_; uint8_t v___x_2895_; 
v_children_2894_ = lean_ctor_get(v_a_2872_, 1);
v___x_2895_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2869_, v_pos_2870_, v_tailPos_2871_, v_children_2894_);
return v___x_2895_;
}
default: 
{
uint8_t v___x_2896_; 
v___x_2896_ = 0;
return v___x_2896_;
}
}
}
else
{
uint8_t v___x_2897_; 
v___x_2897_ = 0;
return v___x_2897_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(lean_object* v_hoverPos_2898_, lean_object* v_pos_2899_, lean_object* v_tailPos_2900_, lean_object* v_as_2901_, size_t v_i_2902_, size_t v_stop_2903_){
_start:
{
uint8_t v___x_2904_; 
v___x_2904_ = lean_usize_dec_eq(v_i_2902_, v_stop_2903_);
if (v___x_2904_ == 0)
{
lean_object* v___x_2905_; uint8_t v___x_2906_; 
v___x_2905_ = lean_array_uget_borrowed(v_as_2901_, v_i_2902_);
v___x_2906_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(v_hoverPos_2898_, v_pos_2899_, v_tailPos_2900_, v___x_2905_);
if (v___x_2906_ == 0)
{
size_t v___x_2907_; size_t v___x_2908_; 
v___x_2907_ = ((size_t)1ULL);
v___x_2908_ = lean_usize_add(v_i_2902_, v___x_2907_);
v_i_2902_ = v___x_2908_;
goto _start;
}
else
{
return v___x_2906_;
}
}
else
{
uint8_t v___x_2910_; 
v___x_2910_ = 0;
return v___x_2910_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1___boxed(lean_object* v_hoverPos_2911_, lean_object* v_pos_2912_, lean_object* v_tailPos_2913_, lean_object* v_as_2914_, lean_object* v_i_2915_, lean_object* v_stop_2916_){
_start:
{
size_t v_i_boxed_2917_; size_t v_stop_boxed_2918_; uint8_t v_res_2919_; lean_object* v_r_2920_; 
v_i_boxed_2917_ = lean_unbox_usize(v_i_2915_);
lean_dec(v_i_2915_);
v_stop_boxed_2918_ = lean_unbox_usize(v_stop_2916_);
lean_dec(v_stop_2916_);
v_res_2919_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_2911_, v_pos_2912_, v_tailPos_2913_, v_as_2914_, v_i_boxed_2917_, v_stop_boxed_2918_);
lean_dec_ref(v_as_2914_);
lean_dec(v_tailPos_2913_);
lean_dec(v_pos_2912_);
lean_dec(v_hoverPos_2911_);
v_r_2920_ = lean_box(v_res_2919_);
return v_r_2920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1___boxed(lean_object* v_hoverPos_2921_, lean_object* v_pos_2922_, lean_object* v_tailPos_2923_, lean_object* v_as_2924_, lean_object* v_i_2925_, lean_object* v_stop_2926_){
_start:
{
size_t v_i_boxed_2927_; size_t v_stop_boxed_2928_; uint8_t v_res_2929_; lean_object* v_r_2930_; 
v_i_boxed_2927_ = lean_unbox_usize(v_i_2925_);
lean_dec(v_i_2925_);
v_stop_boxed_2928_ = lean_unbox_usize(v_stop_2926_);
lean_dec(v_stop_2926_);
v_res_2929_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(v_hoverPos_2921_, v_pos_2922_, v_tailPos_2923_, v_as_2924_, v_i_boxed_2927_, v_stop_boxed_2928_);
lean_dec_ref(v_as_2924_);
lean_dec(v_tailPos_2923_);
lean_dec(v_pos_2922_);
lean_dec(v_hoverPos_2921_);
v_r_2930_ = lean_box(v_res_2929_);
return v_r_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0___boxed(lean_object* v_hoverPos_2931_, lean_object* v_pos_2932_, lean_object* v_tailPos_2933_, lean_object* v_t_2934_){
_start:
{
uint8_t v_res_2935_; lean_object* v_r_2936_; 
v_res_2935_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2931_, v_pos_2932_, v_tailPos_2933_, v_t_2934_);
lean_dec_ref(v_t_2934_);
lean_dec(v_tailPos_2933_);
lean_dec(v_pos_2932_);
lean_dec(v_hoverPos_2931_);
v_r_2936_ = lean_box(v_res_2935_);
return v_r_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0___boxed(lean_object* v_hoverPos_2937_, lean_object* v_pos_2938_, lean_object* v_tailPos_2939_, lean_object* v_x_2940_){
_start:
{
uint8_t v_res_2941_; lean_object* v_r_2942_; 
v_res_2941_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(v_hoverPos_2937_, v_pos_2938_, v_tailPos_2939_, v_x_2940_);
lean_dec_ref(v_x_2940_);
lean_dec(v_tailPos_2939_);
lean_dec(v_pos_2938_);
lean_dec(v_hoverPos_2937_);
v_r_2942_ = lean_box(v_res_2941_);
return v_r_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___boxed(lean_object* v_hoverPos_2943_, lean_object* v_pos_2944_, lean_object* v_tailPos_2945_, lean_object* v_a_2946_){
_start:
{
uint8_t v_res_2947_; lean_object* v_r_2948_; 
v_res_2947_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(v_hoverPos_2943_, v_pos_2944_, v_tailPos_2945_, v_a_2946_);
lean_dec_ref(v_a_2946_);
lean_dec(v_tailPos_2945_);
lean_dec(v_pos_2944_);
lean_dec(v_hoverPos_2943_);
v_r_2948_ = lean_box(v_res_2947_);
return v_r_2948_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock(lean_object* v_stx_2950_){
_start:
{
lean_object* v___x_2951_; uint8_t v___x_2952_; 
v___x_2951_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock___closed__0));
lean_inc(v_stx_2950_);
v___x_2952_ = l_Lean_Syntax_isToken(v___x_2951_, v_stx_2950_);
if (v___x_2952_ == 0)
{
lean_object* v___x_2953_; lean_object* v___x_2954_; uint8_t v___x_2955_; 
v___x_2953_ = l_Lean_Syntax_getNumArgs(v_stx_2950_);
v___x_2954_ = lean_unsigned_to_nat(2u);
v___x_2955_ = lean_nat_dec_eq(v___x_2953_, v___x_2954_);
lean_dec(v___x_2953_);
if (v___x_2955_ == 0)
{
lean_dec(v_stx_2950_);
return v___x_2955_;
}
else
{
lean_object* v___x_2956_; lean_object* v___x_2957_; uint8_t v___x_2958_; 
v___x_2956_ = lean_unsigned_to_nat(0u);
v___x_2957_ = l_Lean_Syntax_getArg(v_stx_2950_, v___x_2956_);
lean_dec(v_stx_2950_);
v___x_2958_ = l_Lean_Syntax_isToken(v___x_2951_, v___x_2957_);
return v___x_2958_;
}
}
else
{
lean_dec(v_stx_2950_);
return v___x_2952_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock___boxed(lean_object* v_stx_2959_){
_start:
{
uint8_t v_res_2960_; lean_object* v_r_2961_; 
v_res_2960_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock(v_stx_2959_);
v_r_2961_ = lean_box(v_res_2960_);
return v_r_2961_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(lean_object* v_x_2962_, lean_object* v_x_2963_){
_start:
{
if (lean_obj_tag(v_x_2962_) == 0)
{
if (lean_obj_tag(v_x_2963_) == 0)
{
uint8_t v___x_2964_; 
v___x_2964_ = 1;
return v___x_2964_;
}
else
{
uint8_t v___x_2965_; 
v___x_2965_ = 0;
return v___x_2965_;
}
}
else
{
if (lean_obj_tag(v_x_2963_) == 0)
{
uint8_t v___x_2966_; 
v___x_2966_ = 0;
return v___x_2966_;
}
else
{
lean_object* v_val_2967_; lean_object* v_val_2968_; uint8_t v___x_2969_; 
v_val_2967_ = lean_ctor_get(v_x_2962_, 0);
v_val_2968_ = lean_ctor_get(v_x_2963_, 0);
v___x_2969_ = lean_nat_dec_eq(v_val_2967_, v_val_2968_);
return v___x_2969_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4___boxed(lean_object* v_x_2970_, lean_object* v_x_2971_){
_start:
{
uint8_t v_res_2972_; lean_object* v_r_2973_; 
v_res_2972_ = l_instBEqOption_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(v_x_2970_, v_x_2971_);
lean_dec(v_x_2971_);
lean_dec(v_x_2970_);
v_r_2973_ = lean_box(v_res_2972_);
return v_r_2973_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(lean_object* v_hoverCol_2974_, lean_object* v_col_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_){
_start:
{
if (lean_obj_tag(v_a_2976_) == 0)
{
lean_object* v___x_2978_; 
v___x_2978_ = l_List_reverse___redArg(v_a_2977_);
return v___x_2978_;
}
else
{
lean_object* v_head_2979_; lean_object* v_tail_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_3004_; 
v_head_2979_ = lean_ctor_get(v_a_2976_, 0);
v_tail_2980_ = lean_ctor_get(v_a_2976_, 1);
v_isSharedCheck_3004_ = !lean_is_exclusive(v_a_2976_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2982_ = v_a_2976_;
v_isShared_2983_ = v_isSharedCheck_3004_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_tail_2980_);
lean_inc(v_head_2979_);
lean_dec(v_a_2976_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_3004_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___y_2985_; uint8_t v_hangingBy_2990_; 
v_hangingBy_2990_ = lean_ctor_get_uint8(v_head_2979_, sizeof(void*)*3 + 2);
if (v_hangingBy_2990_ == 0)
{
v___y_2985_ = v_head_2979_;
goto v___jp_2984_;
}
else
{
lean_object* v_ctxInfo_2991_; lean_object* v_tacticInfo_2992_; uint8_t v_useAfter_2993_; lean_object* v_priority_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3003_; 
v_ctxInfo_2991_ = lean_ctor_get(v_head_2979_, 0);
v_tacticInfo_2992_ = lean_ctor_get(v_head_2979_, 1);
v_useAfter_2993_ = lean_ctor_get_uint8(v_head_2979_, sizeof(void*)*3);
v_priority_2994_ = lean_ctor_get(v_head_2979_, 2);
v_isSharedCheck_3003_ = !lean_is_exclusive(v_head_2979_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2996_ = v_head_2979_;
v_isShared_2997_ = v_isSharedCheck_3003_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_priority_2994_);
lean_inc(v_tacticInfo_2992_);
lean_inc(v_ctxInfo_2991_);
lean_dec(v_head_2979_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3003_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
uint8_t v___x_2998_; uint8_t v___x_2999_; lean_object* v___x_3001_; 
v___x_2998_ = lean_nat_dec_le(v_hoverCol_2974_, v_col_2975_);
v___x_2999_ = 0;
if (v_isShared_2997_ == 0)
{
v___x_3001_ = v___x_2996_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_ctxInfo_2991_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v_tacticInfo_2992_);
lean_ctor_set(v_reuseFailAlloc_3002_, 2, v_priority_2994_);
lean_ctor_set_uint8(v_reuseFailAlloc_3002_, sizeof(void*)*3, v_useAfter_2993_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_ctor_set_uint8(v___x_3001_, sizeof(void*)*3 + 1, v___x_2998_);
lean_ctor_set_uint8(v___x_3001_, sizeof(void*)*3 + 2, v___x_2999_);
v___y_2985_ = v___x_3001_;
goto v___jp_2984_;
}
}
}
v___jp_2984_:
{
lean_object* v___x_2987_; 
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 1, v_a_2977_);
lean_ctor_set(v___x_2982_, 0, v___y_2985_);
v___x_2987_ = v___x_2982_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v___y_2985_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v_a_2977_);
v___x_2987_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
v_a_2976_ = v_tail_2980_;
v_a_2977_ = v___x_2987_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0___boxed(lean_object* v_hoverCol_3005_, lean_object* v_col_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(v_hoverCol_3005_, v_col_3006_, v_a_3007_, v_a_3008_);
lean_dec(v_col_3006_);
lean_dec(v_hoverCol_3005_);
return v_res_3009_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(lean_object* v_x_3010_){
_start:
{
if (lean_obj_tag(v_x_3010_) == 0)
{
uint8_t v___x_3011_; 
v___x_3011_ = 1;
return v___x_3011_;
}
else
{
lean_object* v_head_3012_; uint8_t v_indented_3013_; 
v_head_3012_ = lean_ctor_get(v_x_3010_, 0);
v_indented_3013_ = lean_ctor_get_uint8(v_head_3012_, sizeof(void*)*3 + 1);
if (v_indented_3013_ == 0)
{
return v_indented_3013_;
}
else
{
lean_object* v_tail_3014_; 
v_tail_3014_ = lean_ctor_get(v_x_3010_, 1);
v_x_3010_ = v_tail_3014_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1___boxed(lean_object* v_x_3016_){
_start:
{
uint8_t v_res_3017_; lean_object* v_r_3018_; 
v_res_3017_ = l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(v_x_3016_);
lean_dec(v_x_3016_);
v_r_3018_ = lean_box(v_res_3017_);
return v_r_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0(lean_object* v_text_3019_, lean_object* v_column_3020_, lean_object* v_hoverPos_3021_, lean_object* v_ctx_3022_, lean_object* v_i_3023_, lean_object* v_cs_3024_, lean_object* v_gs_3025_){
_start:
{
if (lean_obj_tag(v_i_3023_) == 0)
{
lean_object* v_i_3026_; lean_object* v___x_3027_; 
v_i_3026_ = lean_ctor_get(v_i_3023_, 0);
v___x_3027_ = l_Lean_Elab_Info_pos_x3f(v_i_3023_);
if (lean_obj_tag(v___x_3027_) == 1)
{
lean_object* v_val_3028_; lean_object* v___x_3029_; 
v_val_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_val_3028_);
lean_dec_ref_known(v___x_3027_, 1);
v___x_3029_ = l_Lean_Elab_Info_tailPos_x3f(v_i_3023_);
if (lean_obj_tag(v___x_3029_) == 1)
{
lean_object* v_val_3030_; lean_object* v___x_3031_; lean_object* v_column_3032_; lean_object* v_source_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3083_; 
v_val_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_val_3030_);
lean_dec_ref_known(v___x_3029_, 1);
lean_inc_ref(v_text_3019_);
v___x_3031_ = l_Lean_FileMap_toPosition(v_text_3019_, v_val_3028_);
v_column_3032_ = lean_ctor_get(v___x_3031_, 1);
lean_inc(v_column_3032_);
lean_dec_ref(v___x_3031_);
v_source_3033_ = lean_ctor_get(v_text_3019_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v_text_3019_);
if (v_isSharedCheck_3083_ == 0)
{
lean_object* v_unused_3084_; 
v_unused_3084_ = lean_ctor_get(v_text_3019_, 1);
lean_dec(v_unused_3084_);
v___x_3035_ = v_text_3019_;
v_isShared_3036_ = v_isSharedCheck_3083_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_source_3033_);
lean_dec(v_text_3019_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3083_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3037_; uint8_t v___y_3039_; uint8_t v___y_3040_; uint8_t v___y_3041_; lean_object* v___y_3042_; lean_object* v_gs_3047_; lean_object* v___x_3048_; lean_object* v_trailSize_3049_; lean_object* v___x_3050_; uint8_t v___y_3052_; uint8_t v___y_3059_; uint8_t v___y_3066_; uint8_t v___y_3068_; uint8_t v___y_3073_; uint8_t v___x_3074_; 
v___x_3037_ = lean_box(0);
v_gs_3047_ = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(v_column_3020_, v_column_3032_, v_gs_3025_, v___x_3037_);
v___x_3048_ = l_Lean_Elab_Info_stx(v_i_3023_);
v_trailSize_3049_ = l_Lean_Syntax_getTrailingSize(v___x_3048_);
v___x_3050_ = lean_nat_add(v_val_3030_, v_trailSize_3049_);
v___x_3074_ = lean_nat_dec_le(v_val_3028_, v_hoverPos_3021_);
if (v___x_3074_ == 0)
{
lean_dec(v_trailSize_3049_);
lean_dec_ref(v_source_3033_);
v___y_3073_ = v___x_3074_;
goto v___jp_3072_;
}
else
{
lean_object* v___x_3075_; uint8_t v_atEOF_3076_; lean_object* v___y_3078_; lean_object* v___x_3081_; uint8_t v___x_3082_; 
v___x_3075_ = lean_string_utf8_byte_size(v_source_3033_);
lean_dec_ref(v_source_3033_);
v_atEOF_3076_ = lean_nat_dec_eq(v___x_3050_, v___x_3075_);
v___x_3081_ = lean_unsigned_to_nat(1u);
v___x_3082_ = lean_nat_dec_le(v___x_3081_, v_trailSize_3049_);
if (v___x_3082_ == 0)
{
lean_dec(v_trailSize_3049_);
v___y_3078_ = v___x_3081_;
goto v___jp_3077_;
}
else
{
v___y_3078_ = v_trailSize_3049_;
goto v___jp_3077_;
}
v___jp_3077_:
{
lean_object* v___x_3079_; uint8_t v___x_3080_; 
v___x_3079_ = lean_nat_add(v_val_3030_, v___y_3078_);
lean_dec(v___y_3078_);
v___x_3080_ = lean_nat_dec_lt(v_hoverPos_3021_, v___x_3079_);
lean_dec(v___x_3079_);
if (v___x_3080_ == 0)
{
v___y_3073_ = v_atEOF_3076_;
goto v___jp_3072_;
}
else
{
v___y_3068_ = v___x_3080_;
goto v___jp_3067_;
}
}
}
v___jp_3038_:
{
lean_object* v___x_3043_; lean_object* v___x_3045_; 
lean_inc_ref(v_i_3026_);
v___x_3043_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3043_, 0, v_ctx_3022_);
lean_ctor_set(v___x_3043_, 1, v_i_3026_);
lean_ctor_set(v___x_3043_, 2, v___y_3042_);
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*3, v___y_3041_);
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*3 + 1, v___y_3039_);
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*3 + 2, v___y_3040_);
if (v_isShared_3036_ == 0)
{
lean_ctor_set_tag(v___x_3035_, 1);
lean_ctor_set(v___x_3035_, 1, v___x_3037_);
lean_ctor_set(v___x_3035_, 0, v___x_3043_);
v___x_3045_ = v___x_3035_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3043_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v___x_3037_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
v___jp_3051_:
{
uint8_t v___x_3053_; uint8_t v___x_3054_; uint8_t v___x_3055_; 
v___x_3053_ = lean_nat_dec_lt(v_column_3020_, v_column_3032_);
lean_dec(v_column_3032_);
v___x_3054_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock(v___x_3048_);
v___x_3055_ = lean_nat_dec_eq(v_hoverPos_3021_, v___x_3050_);
lean_dec(v___x_3050_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; 
v___x_3056_ = lean_unsigned_to_nat(1u);
v___y_3039_ = v___x_3053_;
v___y_3040_ = v___x_3054_;
v___y_3041_ = v___y_3052_;
v___y_3042_ = v___x_3056_;
goto v___jp_3038_;
}
else
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_unsigned_to_nat(0u);
v___y_3039_ = v___x_3053_;
v___y_3040_ = v___x_3054_;
v___y_3041_ = v___y_3052_;
v___y_3042_ = v___x_3057_;
goto v___jp_3038_;
}
}
v___jp_3058_:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; 
v___x_3060_ = lean_unsigned_to_nat(1u);
v___x_3061_ = lean_nat_add(v_val_3028_, v___x_3060_);
v___x_3062_ = lean_nat_dec_le(v___x_3061_, v_hoverPos_3021_);
lean_dec(v___x_3061_);
if (v___x_3062_ == 0)
{
lean_dec(v_val_3030_);
lean_dec(v_val_3028_);
v___y_3052_ = v___x_3062_;
goto v___jp_3051_;
}
else
{
uint8_t v___x_3063_; 
v___x_3063_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_3021_, v_val_3028_, v_val_3030_, v_cs_3024_);
lean_dec(v_val_3030_);
lean_dec(v_val_3028_);
if (v___x_3063_ == 0)
{
v___y_3052_ = v___y_3059_;
goto v___jp_3051_;
}
else
{
uint8_t v___x_3064_; 
v___x_3064_ = 0;
v___y_3052_ = v___x_3064_;
goto v___jp_3051_;
}
}
}
v___jp_3065_:
{
if (v___y_3066_ == 0)
{
lean_dec(v___x_3050_);
lean_dec(v___x_3048_);
lean_del_object(v___x_3035_);
lean_dec(v_column_3032_);
lean_dec(v_val_3030_);
lean_dec(v_val_3028_);
lean_dec_ref(v_ctx_3022_);
return v_gs_3047_;
}
else
{
lean_dec(v_gs_3047_);
v___y_3059_ = v___y_3066_;
goto v___jp_3058_;
}
}
v___jp_3067_:
{
uint8_t v___x_3069_; 
v___x_3069_ = l_List_isEmpty___redArg(v_gs_3047_);
if (v___x_3069_ == 0)
{
uint8_t v___x_3070_; 
v___x_3070_ = lean_nat_dec_le(v_val_3030_, v_hoverPos_3021_);
if (v___x_3070_ == 0)
{
v___y_3066_ = v___x_3070_;
goto v___jp_3065_;
}
else
{
uint8_t v___x_3071_; 
v___x_3071_ = l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(v_gs_3047_);
v___y_3066_ = v___x_3071_;
goto v___jp_3065_;
}
}
else
{
lean_dec(v_gs_3047_);
v___y_3059_ = v___y_3068_;
goto v___jp_3058_;
}
}
v___jp_3072_:
{
if (v___y_3073_ == 0)
{
lean_dec(v___x_3050_);
lean_dec(v___x_3048_);
lean_del_object(v___x_3035_);
lean_dec(v_column_3032_);
lean_dec(v_val_3030_);
lean_dec(v_val_3028_);
lean_dec_ref(v_ctx_3022_);
return v_gs_3047_;
}
else
{
v___y_3068_ = v___y_3073_;
goto v___jp_3067_;
}
}
}
}
else
{
lean_dec(v___x_3029_);
lean_dec(v_val_3028_);
lean_dec_ref(v_ctx_3022_);
lean_dec_ref(v_text_3019_);
return v_gs_3025_;
}
}
else
{
lean_dec(v___x_3027_);
lean_dec_ref(v_ctx_3022_);
lean_dec_ref(v_text_3019_);
return v_gs_3025_;
}
}
else
{
lean_dec_ref(v_ctx_3022_);
lean_dec_ref(v_text_3019_);
return v_gs_3025_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0___boxed(lean_object* v_text_3085_, lean_object* v_column_3086_, lean_object* v_hoverPos_3087_, lean_object* v_ctx_3088_, lean_object* v_i_3089_, lean_object* v_cs_3090_, lean_object* v_gs_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0(v_text_3085_, v_column_3086_, v_hoverPos_3087_, v_ctx_3088_, v_i_3089_, v_cs_3090_, v_gs_3091_);
lean_dec_ref(v_cs_3090_);
lean_dec_ref(v_i_3089_);
lean_dec(v_hoverPos_3087_);
lean_dec(v_column_3086_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3_spec__3(lean_object* v_x_3093_, lean_object* v_x_3094_){
_start:
{
if (lean_obj_tag(v_x_3094_) == 0)
{
lean_inc(v_x_3093_);
return v_x_3093_;
}
else
{
lean_object* v_head_3095_; lean_object* v_tail_3096_; uint8_t v___x_3097_; 
v_head_3095_ = lean_ctor_get(v_x_3094_, 0);
v_tail_3096_ = lean_ctor_get(v_x_3094_, 1);
v___x_3097_ = lean_nat_dec_le(v_x_3093_, v_head_3095_);
if (v___x_3097_ == 0)
{
v_x_3094_ = v_tail_3096_;
goto _start;
}
else
{
v_x_3093_ = v_head_3095_;
v_x_3094_ = v_tail_3096_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3_spec__3___boxed(lean_object* v_x_3100_, lean_object* v_x_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3_spec__3(v_x_3100_, v_x_3101_);
lean_dec(v_x_3101_);
lean_dec(v_x_3100_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(lean_object* v_x_3103_){
_start:
{
if (lean_obj_tag(v_x_3103_) == 0)
{
lean_object* v___x_3104_; 
v___x_3104_ = lean_box(0);
return v___x_3104_;
}
else
{
lean_object* v_head_3105_; lean_object* v_tail_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v_head_3105_ = lean_ctor_get(v_x_3103_, 0);
v_tail_3106_ = lean_ctor_get(v_x_3103_, 1);
v___x_3107_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3_spec__3(v_head_3105_, v_tail_3106_);
v___x_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
return v___x_3108_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3___boxed(lean_object* v_x_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(v_x_3109_);
lean_dec(v_x_3109_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2(lean_object* v_a_3111_, lean_object* v_a_3112_){
_start:
{
if (lean_obj_tag(v_a_3111_) == 0)
{
lean_object* v___x_3113_; 
v___x_3113_ = l_List_reverse___redArg(v_a_3112_);
return v___x_3113_;
}
else
{
lean_object* v_head_3114_; lean_object* v_tail_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3124_; 
v_head_3114_ = lean_ctor_get(v_a_3111_, 0);
v_tail_3115_ = lean_ctor_get(v_a_3111_, 1);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_a_3111_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3117_ = v_a_3111_;
v_isShared_3118_ = v_isSharedCheck_3124_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_tail_3115_);
lean_inc(v_head_3114_);
lean_dec(v_a_3111_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3124_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v_priority_3119_; lean_object* v___x_3121_; 
v_priority_3119_ = lean_ctor_get(v_head_3114_, 2);
lean_inc(v_priority_3119_);
lean_dec(v_head_3114_);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 1, v_a_3112_);
lean_ctor_set(v___x_3117_, 0, v_priority_3119_);
v___x_3121_ = v___x_3117_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_priority_3119_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v_a_3112_);
v___x_3121_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
v_a_3111_ = v_tail_3115_;
v_a_3112_ = v___x_3121_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__5(lean_object* v_maxPrio_x3f_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_){
_start:
{
if (lean_obj_tag(v_a_3126_) == 0)
{
lean_object* v___x_3128_; 
v___x_3128_ = l_List_reverse___redArg(v_a_3127_);
return v___x_3128_;
}
else
{
lean_object* v_head_3129_; lean_object* v_tail_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3142_; 
v_head_3129_ = lean_ctor_get(v_a_3126_, 0);
v_tail_3130_ = lean_ctor_get(v_a_3126_, 1);
v_isSharedCheck_3142_ = !lean_is_exclusive(v_a_3126_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3132_ = v_a_3126_;
v_isShared_3133_ = v_isSharedCheck_3142_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_tail_3130_);
lean_inc(v_head_3129_);
lean_dec(v_a_3126_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3142_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v_priority_3134_; lean_object* v___x_3135_; uint8_t v___x_3136_; 
v_priority_3134_ = lean_ctor_get(v_head_3129_, 2);
lean_inc(v_priority_3134_);
v___x_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3135_, 0, v_priority_3134_);
v___x_3136_ = l_instBEqOption_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(v___x_3135_, v_maxPrio_x3f_3125_);
lean_dec_ref_known(v___x_3135_, 1);
if (v___x_3136_ == 0)
{
lean_del_object(v___x_3132_);
lean_dec(v_head_3129_);
v_a_3126_ = v_tail_3130_;
goto _start;
}
else
{
lean_object* v___x_3139_; 
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 1, v_a_3127_);
v___x_3139_ = v___x_3132_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_head_3129_);
lean_ctor_set(v_reuseFailAlloc_3141_, 1, v_a_3127_);
v___x_3139_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
v_a_3126_ = v_tail_3130_;
v_a_3127_ = v___x_3139_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__5___boxed(lean_object* v_maxPrio_x3f_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__5(v_maxPrio_x3f_3143_, v_a_3144_, v_a_3145_);
lean_dec(v_maxPrio_x3f_3143_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f(lean_object* v_text_3147_, lean_object* v_t_3148_, lean_object* v_hoverPos_3149_){
_start:
{
lean_object* v___x_3150_; lean_object* v_column_3151_; lean_object* v___f_3152_; lean_object* v_gs_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v_maxPrio_x3f_3156_; lean_object* v___x_3157_; 
lean_inc_ref(v_text_3147_);
v___x_3150_ = l_Lean_FileMap_toPosition(v_text_3147_, v_hoverPos_3149_);
v_column_3151_ = lean_ctor_get(v___x_3150_, 1);
lean_inc(v_column_3151_);
lean_dec_ref(v___x_3150_);
v___f_3152_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0___boxed), 7, 3);
lean_closure_set(v___f_3152_, 0, v_text_3147_);
lean_closure_set(v___f_3152_, 1, v_column_3151_);
lean_closure_set(v___f_3152_, 2, v_hoverPos_3149_);
v_gs_3153_ = l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg(v___f_3152_, v_t_3148_);
v___x_3154_ = lean_box(0);
lean_inc(v_gs_3153_);
v___x_3155_ = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2(v_gs_3153_, v___x_3154_);
v_maxPrio_x3f_3156_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(v___x_3155_);
lean_dec(v___x_3155_);
v___x_3157_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__5(v_maxPrio_x3f_3156_, v_gs_3153_, v___x_3154_);
lean_dec(v_maxPrio_x3f_3156_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(lean_object* v___x_3158_, uint8_t v___y_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_){
_start:
{
if (lean_obj_tag(v_a_3160_) == 0)
{
lean_object* v___x_3162_; 
v___x_3162_ = l_List_reverse___redArg(v_a_3161_);
return v___x_3162_;
}
else
{
lean_object* v_head_3163_; lean_object* v_snd_3164_; lean_object* v_tail_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3180_; 
v_head_3163_ = lean_ctor_get(v_a_3160_, 0);
lean_inc(v_head_3163_);
v_snd_3164_ = lean_ctor_get(v_head_3163_, 1);
v_tail_3165_ = lean_ctor_get(v_a_3160_, 1);
v_isSharedCheck_3180_ = !lean_is_exclusive(v_a_3160_);
if (v_isSharedCheck_3180_ == 0)
{
lean_object* v_unused_3181_; 
v_unused_3181_ = lean_ctor_get(v_a_3160_, 0);
lean_dec(v_unused_3181_);
v___x_3167_ = v_a_3160_;
v_isShared_3168_ = v_isSharedCheck_3180_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_tail_3165_);
lean_dec(v_a_3160_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3180_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v_info_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; uint8_t v___x_3173_; 
v_info_3169_ = lean_ctor_get(v_snd_3164_, 1);
v___x_3170_ = l_Lean_Elab_Info_stx(v_info_3169_);
v___x_3171_ = lean_unsigned_to_nat(0u);
v___x_3172_ = l_Lean_Syntax_getArg(v___x_3158_, v___x_3171_);
v___x_3173_ = l_Lean_Syntax_structEq(v___x_3170_, v___x_3172_);
lean_dec(v___x_3172_);
lean_dec(v___x_3170_);
if (v___x_3173_ == 0)
{
if (v___y_3159_ == 0)
{
lean_del_object(v___x_3167_);
lean_dec(v_head_3163_);
v_a_3160_ = v_tail_3165_;
goto _start;
}
else
{
lean_object* v___x_3176_; 
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 1, v_a_3161_);
v___x_3176_ = v___x_3167_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_head_3163_);
lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_a_3161_);
v___x_3176_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
v_a_3160_ = v_tail_3165_;
v_a_3161_ = v___x_3176_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_3167_);
lean_dec(v_head_3163_);
v_a_3160_ = v_tail_3165_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0___boxed(lean_object* v___x_3182_, lean_object* v___y_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_){
_start:
{
uint8_t v___y_1198__boxed_3186_; lean_object* v_res_3187_; 
v___y_1198__boxed_3186_ = lean_unbox(v___y_3183_);
v_res_3187_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(v___x_3182_, v___y_1198__boxed_3186_, v_a_3184_, v_a_3185_);
lean_dec(v___x_3182_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0(lean_object* v_ctx_3194_, lean_object* v_info_3195_, lean_object* v_children_3196_, lean_object* v_results_3197_){
_start:
{
lean_object* v___x_3198_; uint8_t v___y_3200_; lean_object* v___x_3203_; uint8_t v___x_3204_; 
v___x_3198_ = l_Lean_Elab_Info_stx(v_info_3195_);
v___x_3203_ = ((lean_object*)(l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1));
lean_inc(v___x_3198_);
v___x_3204_ = l_Lean_Syntax_isOfKind(v___x_3198_, v___x_3203_);
if (v___x_3204_ == 0)
{
v___y_3200_ = v___x_3204_;
goto v___jp_3199_;
}
else
{
lean_object* v___x_3205_; lean_object* v___x_3206_; uint8_t v___x_3207_; 
v___x_3205_ = lean_unsigned_to_nat(0u);
v___x_3206_ = l_Lean_Syntax_getArg(v___x_3198_, v___x_3205_);
v___x_3207_ = l_Lean_Syntax_isIdent(v___x_3206_);
lean_dec(v___x_3206_);
v___y_3200_ = v___x_3207_;
goto v___jp_3199_;
}
v___jp_3199_:
{
if (v___y_3200_ == 0)
{
lean_dec(v___x_3198_);
return v_results_3197_;
}
else
{
lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3201_ = lean_box(0);
v___x_3202_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(v___x_3198_, v___y_3200_, v_results_3197_, v___x_3201_);
lean_dec(v___x_3198_);
return v___x_3202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___boxed(lean_object* v_ctx_3208_, lean_object* v_info_3209_, lean_object* v_children_3210_, lean_object* v_results_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0(v_ctx_3208_, v_info_3209_, v_children_3210_, v_results_3211_);
lean_dec_ref(v_children_3210_);
lean_dec_ref(v_info_3209_);
lean_dec_ref(v_ctx_3208_);
return v_res_3212_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(lean_object* v_x_3213_, lean_object* v_x_3214_){
_start:
{
if (lean_obj_tag(v_x_3213_) == 0)
{
if (lean_obj_tag(v_x_3214_) == 0)
{
uint8_t v___x_3215_; 
v___x_3215_ = 1;
return v___x_3215_;
}
else
{
uint8_t v___x_3216_; 
v___x_3216_ = 0;
return v___x_3216_;
}
}
else
{
if (lean_obj_tag(v_x_3214_) == 0)
{
uint8_t v___x_3217_; 
v___x_3217_ = 0;
return v___x_3217_;
}
else
{
lean_object* v_val_3218_; lean_object* v_val_3219_; uint8_t v___x_3220_; 
v_val_3218_ = lean_ctor_get(v_x_3213_, 0);
v_val_3219_ = lean_ctor_get(v_x_3214_, 0);
v___x_3220_ = l_Lean_Elab_instBEqHoverableInfoPrio_beq(v_val_3218_, v_val_3219_);
return v___x_3220_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4___boxed(lean_object* v_x_3221_, lean_object* v_x_3222_){
_start:
{
uint8_t v_res_3223_; lean_object* v_r_3224_; 
v_res_3223_ = l_instBEqOption_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(v_x_3221_, v_x_3222_);
lean_dec(v_x_3222_);
lean_dec(v_x_3221_);
v_r_3224_ = lean_box(v_res_3223_);
return v_r_3224_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5(lean_object* v_maxPrio_x3f_3225_, lean_object* v_x_3226_){
_start:
{
if (lean_obj_tag(v_x_3226_) == 0)
{
lean_object* v___x_3227_; 
v___x_3227_ = lean_box(0);
return v___x_3227_;
}
else
{
lean_object* v_head_3228_; lean_object* v_tail_3229_; lean_object* v_fst_3230_; lean_object* v___x_3231_; uint8_t v___x_3232_; 
v_head_3228_ = lean_ctor_get(v_x_3226_, 0);
v_tail_3229_ = lean_ctor_get(v_x_3226_, 1);
v_fst_3230_ = lean_ctor_get(v_head_3228_, 0);
lean_inc(v_fst_3230_);
v___x_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3231_, 0, v_fst_3230_);
v___x_3232_ = l_instBEqOption_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(v___x_3231_, v_maxPrio_x3f_3225_);
lean_dec_ref_known(v___x_3231_, 1);
if (v___x_3232_ == 0)
{
v_x_3226_ = v_tail_3229_;
goto _start;
}
else
{
lean_object* v___x_3234_; 
lean_inc(v_head_3228_);
v___x_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3234_, 0, v_head_3228_);
return v___x_3234_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5___boxed(lean_object* v_maxPrio_x3f_3235_, lean_object* v_x_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5(v_maxPrio_x3f_3235_, v_x_3236_);
lean_dec(v_x_3236_);
lean_dec(v_maxPrio_x3f_3235_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(lean_object* v_x_3238_, lean_object* v_x_3239_){
_start:
{
if (lean_obj_tag(v_x_3239_) == 0)
{
lean_inc_ref(v_x_3238_);
return v_x_3238_;
}
else
{
lean_object* v_head_3240_; lean_object* v_tail_3241_; uint8_t v___x_3242_; 
v_head_3240_ = lean_ctor_get(v_x_3239_, 0);
v_tail_3241_ = lean_ctor_get(v_x_3239_, 1);
v___x_3242_ = l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(v_x_3238_, v_head_3240_);
if (v___x_3242_ == 2)
{
v_x_3239_ = v_tail_3241_;
goto _start;
}
else
{
v_x_3238_ = v_head_3240_;
v_x_3239_ = v_tail_3241_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4___boxed(lean_object* v_x_3245_, lean_object* v_x_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(v_x_3245_, v_x_3246_);
lean_dec(v_x_3246_);
lean_dec_ref(v_x_3245_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(lean_object* v_x_3248_){
_start:
{
if (lean_obj_tag(v_x_3248_) == 0)
{
lean_object* v___x_3249_; 
v___x_3249_ = lean_box(0);
return v___x_3249_;
}
else
{
lean_object* v_head_3250_; lean_object* v_tail_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v_head_3250_ = lean_ctor_get(v_x_3248_, 0);
v_tail_3251_ = lean_ctor_get(v_x_3248_, 1);
v___x_3252_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(v_head_3250_, v_tail_3251_);
v___x_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3252_);
return v___x_3253_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3___boxed(lean_object* v_x_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(v_x_3254_);
lean_dec(v_x_3254_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__1(lean_object* v_a_3256_, lean_object* v_a_3257_){
_start:
{
if (lean_obj_tag(v_a_3256_) == 0)
{
lean_object* v___x_3258_; 
v___x_3258_ = lean_array_to_list(v_a_3257_);
return v___x_3258_;
}
else
{
lean_object* v_head_3259_; 
v_head_3259_ = lean_ctor_get(v_a_3256_, 0);
if (lean_obj_tag(v_head_3259_) == 0)
{
lean_object* v_tail_3260_; 
v_tail_3260_ = lean_ctor_get(v_a_3256_, 1);
lean_inc(v_tail_3260_);
lean_dec_ref_known(v_a_3256_, 2);
v_a_3256_ = v_tail_3260_;
goto _start;
}
else
{
lean_object* v_val_3262_; 
v_val_3262_ = lean_ctor_get(v_head_3259_, 0);
if (lean_obj_tag(v_val_3262_) == 0)
{
lean_object* v_tail_3263_; 
v_tail_3263_ = lean_ctor_get(v_a_3256_, 1);
lean_inc(v_tail_3263_);
lean_dec_ref_known(v_a_3256_, 2);
v_a_3256_ = v_tail_3263_;
goto _start;
}
else
{
lean_object* v_tail_3265_; lean_object* v_val_3266_; lean_object* v___x_3267_; 
lean_inc_ref(v_val_3262_);
v_tail_3265_ = lean_ctor_get(v_a_3256_, 1);
lean_inc(v_tail_3265_);
lean_dec_ref_known(v_a_3256_, 2);
v_val_3266_ = lean_ctor_get(v_val_3262_, 0);
lean_inc(v_val_3266_);
lean_dec_ref_known(v_val_3262_, 1);
v___x_3267_ = lean_array_push(v_a_3257_, v_val_3266_);
v_a_3256_ = v_tail_3265_;
v_a_3257_ = v___x_3267_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__2(lean_object* v_a_3269_, lean_object* v_a_3270_){
_start:
{
if (lean_obj_tag(v_a_3269_) == 0)
{
lean_object* v___x_3271_; 
v___x_3271_ = l_List_reverse___redArg(v_a_3270_);
return v___x_3271_;
}
else
{
lean_object* v_head_3272_; lean_object* v_tail_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3282_; 
v_head_3272_ = lean_ctor_get(v_a_3269_, 0);
v_tail_3273_ = lean_ctor_get(v_a_3269_, 1);
v_isSharedCheck_3282_ = !lean_is_exclusive(v_a_3269_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3275_ = v_a_3269_;
v_isShared_3276_ = v_isSharedCheck_3282_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_tail_3273_);
lean_inc(v_head_3272_);
lean_dec(v_a_3269_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3282_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v_fst_3277_; lean_object* v___x_3279_; 
v_fst_3277_ = lean_ctor_get(v_head_3272_, 0);
lean_inc(v_fst_3277_);
lean_dec(v_head_3272_);
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 1, v_a_3270_);
lean_ctor_set(v___x_3275_, 0, v_fst_3277_);
v___x_3279_ = v___x_3275_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_fst_3277_);
lean_ctor_set(v_reuseFailAlloc_3281_, 1, v_a_3270_);
v___x_3279_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
v_a_3269_ = v_tail_3273_;
v_a_3270_ = v___x_3279_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1(lean_object* v_filter_3283_, lean_object* v_hoverPos_3284_, uint8_t v_includeStop_3285_, lean_object* v_ctx_3286_, lean_object* v_info_3287_, lean_object* v_children_3288_, lean_object* v_results_3289_){
_start:
{
lean_object* v___y_3291_; uint8_t v___y_3292_; uint8_t v___y_3293_; uint8_t v___y_3294_; lean_object* v___y_3300_; uint8_t v___y_3301_; uint8_t v___y_3302_; uint8_t v___y_3303_; uint8_t v___y_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v_maxPrio_x3f_3310_; lean_object* v_bestResult_x3f_3311_; 
v___x_3305_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___closed__0));
v___x_3306_ = l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__1(v_results_3289_, v___x_3305_);
lean_inc_ref(v_children_3288_);
lean_inc_ref(v_info_3287_);
lean_inc_ref(v_ctx_3286_);
v___x_3307_ = lean_apply_4(v_filter_3283_, v_ctx_3286_, v_info_3287_, v_children_3288_, v___x_3306_);
v___x_3308_ = lean_box(0);
lean_inc(v___x_3307_);
v___x_3309_ = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__2(v___x_3307_, v___x_3308_);
v_maxPrio_x3f_3310_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(v___x_3309_);
lean_dec(v___x_3309_);
v_bestResult_x3f_3311_ = l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5(v_maxPrio_x3f_3310_, v___x_3307_);
lean_dec(v___x_3307_);
lean_dec(v_maxPrio_x3f_3310_);
if (lean_obj_tag(v_bestResult_x3f_3311_) == 1)
{
lean_dec_ref(v_children_3288_);
lean_dec_ref(v_info_3287_);
lean_dec_ref(v_ctx_3286_);
return v_bestResult_x3f_3311_;
}
else
{
lean_object* v___x_3312_; uint8_t v___y_3314_; uint8_t v___y_3315_; uint8_t v___y_3316_; uint8_t v___y_3330_; lean_object* v___x_3334_; uint8_t v___x_3335_; 
lean_dec(v_bestResult_x3f_3311_);
v___x_3312_ = l_Lean_Elab_Info_stx(v_info_3287_);
v___x_3334_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__1));
lean_inc(v___x_3312_);
v___x_3335_ = l_Lean_Syntax_isOfKind(v___x_3312_, v___x_3334_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; 
lean_inc_ref(v_info_3287_);
v___x_3336_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_3287_);
if (lean_obj_tag(v___x_3336_) == 0)
{
v___y_3330_ = v___x_3335_;
goto v___jp_3329_;
}
else
{
lean_object* v_val_3337_; lean_object* v_elaborator_3338_; lean_object* v___x_3339_; uint8_t v___x_3340_; 
v_val_3337_ = lean_ctor_get(v___x_3336_, 0);
lean_inc(v_val_3337_);
lean_dec_ref_known(v___x_3336_, 1);
v_elaborator_3338_ = lean_ctor_get(v_val_3337_, 0);
lean_inc(v_elaborator_3338_);
lean_dec(v_val_3337_);
v___x_3339_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6));
v___x_3340_ = lean_name_eq(v_elaborator_3338_, v___x_3339_);
lean_dec(v_elaborator_3338_);
v___y_3330_ = v___x_3340_;
goto v___jp_3329_;
}
}
else
{
v___y_3330_ = v___x_3335_;
goto v___jp_3329_;
}
v___jp_3313_:
{
lean_object* v___x_3317_; 
v___x_3317_ = l_Lean_Syntax_getRange_x3f(v___x_3312_, v___y_3315_);
lean_dec(v___x_3312_);
if (lean_obj_tag(v___x_3317_) == 1)
{
lean_object* v_val_3318_; uint8_t v___x_3319_; 
v_val_3318_ = lean_ctor_get(v___x_3317_, 0);
lean_inc(v_val_3318_);
lean_dec_ref_known(v___x_3317_, 1);
v___x_3319_ = l_Lean_Syntax_Range_contains(v_val_3318_, v_hoverPos_3284_, v_includeStop_3285_);
if (v___x_3319_ == 0)
{
lean_object* v___x_3320_; 
lean_dec(v_val_3318_);
lean_dec_ref(v_children_3288_);
lean_dec_ref(v_info_3287_);
lean_dec_ref(v_ctx_3286_);
v___x_3320_ = lean_box(0);
return v___x_3320_;
}
else
{
if (v___y_3316_ == 0)
{
lean_object* v___x_3321_; 
lean_dec(v_val_3318_);
lean_dec_ref(v_children_3288_);
lean_dec_ref(v_info_3287_);
lean_dec_ref(v_ctx_3286_);
v___x_3321_ = lean_box(0);
return v___x_3321_;
}
else
{
lean_object* v_start_3322_; lean_object* v_stop_3323_; uint8_t v_decide_3324_; lean_object* v___x_3325_; 
v_start_3322_ = lean_ctor_get(v_val_3318_, 0);
lean_inc(v_start_3322_);
v_stop_3323_ = lean_ctor_get(v_val_3318_, 1);
lean_inc(v_stop_3323_);
lean_dec(v_val_3318_);
v_decide_3324_ = lean_nat_dec_eq(v_stop_3323_, v_hoverPos_3284_);
v___x_3325_ = lean_nat_sub(v_stop_3323_, v_start_3322_);
lean_dec(v_start_3322_);
lean_dec(v_stop_3323_);
if (lean_obj_tag(v_info_3287_) == 1)
{
lean_object* v_i_3326_; lean_object* v_expr_3327_; 
v_i_3326_ = lean_ctor_get(v_info_3287_, 0);
v_expr_3327_ = lean_ctor_get(v_i_3326_, 3);
if (lean_obj_tag(v_expr_3327_) == 1)
{
v___y_3300_ = v___x_3325_;
v___y_3301_ = v___y_3314_;
v___y_3302_ = v_decide_3324_;
v___y_3303_ = v___y_3315_;
v___y_3304_ = v___y_3315_;
goto v___jp_3299_;
}
else
{
v___y_3300_ = v___x_3325_;
v___y_3301_ = v___y_3314_;
v___y_3302_ = v_decide_3324_;
v___y_3303_ = v___y_3315_;
v___y_3304_ = v___y_3314_;
goto v___jp_3299_;
}
}
else
{
v___y_3300_ = v___x_3325_;
v___y_3301_ = v___y_3314_;
v___y_3302_ = v_decide_3324_;
v___y_3303_ = v___y_3315_;
v___y_3304_ = v___y_3314_;
goto v___jp_3299_;
}
}
}
}
else
{
lean_object* v___x_3328_; 
lean_dec(v___x_3317_);
lean_dec_ref(v_children_3288_);
lean_dec_ref(v_info_3287_);
lean_dec_ref(v_ctx_3286_);
v___x_3328_ = lean_box(0);
return v___x_3328_;
}
}
v___jp_3329_:
{
if (v___y_3330_ == 0)
{
uint8_t v___x_3331_; 
v___x_3331_ = 1;
switch(lean_obj_tag(v_info_3287_))
{
case 7:
{
v___y_3314_ = v___y_3330_;
v___y_3315_ = v___x_3331_;
v___y_3316_ = v___x_3331_;
goto v___jp_3313_;
}
case 5:
{
v___y_3314_ = v___y_3330_;
v___y_3315_ = v___x_3331_;
v___y_3316_ = v___x_3331_;
goto v___jp_3313_;
}
case 6:
{
v___y_3314_ = v___y_3330_;
v___y_3315_ = v___x_3331_;
v___y_3316_ = v___x_3331_;
goto v___jp_3313_;
}
default: 
{
lean_object* v___x_3332_; 
lean_inc_ref(v_info_3287_);
v___x_3332_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_3287_);
if (lean_obj_tag(v___x_3332_) == 0)
{
v___y_3314_ = v___y_3330_;
v___y_3315_ = v___x_3331_;
v___y_3316_ = v___y_3330_;
goto v___jp_3313_;
}
else
{
lean_dec_ref_known(v___x_3332_, 1);
v___y_3314_ = v___y_3330_;
v___y_3315_ = v___x_3331_;
v___y_3316_ = v___x_3331_;
goto v___jp_3313_;
}
}
}
}
else
{
lean_object* v___x_3333_; 
lean_dec(v___x_3312_);
lean_dec_ref(v_children_3288_);
lean_dec_ref(v_info_3287_);
lean_dec_ref(v_ctx_3286_);
v___x_3333_ = lean_box(0);
return v___x_3333_;
}
}
}
v___jp_3290_:
{
lean_object* v_priority_3295_; lean_object* v_result_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v_priority_3295_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_priority_3295_, 0, v___y_3291_);
lean_ctor_set_uint8(v_priority_3295_, sizeof(void*)*1, v___y_3292_);
lean_ctor_set_uint8(v_priority_3295_, sizeof(void*)*1 + 1, v___y_3293_);
lean_ctor_set_uint8(v_priority_3295_, sizeof(void*)*1 + 2, v___y_3294_);
v_result_3296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_result_3296_, 0, v_ctx_3286_);
lean_ctor_set(v_result_3296_, 1, v_info_3287_);
lean_ctor_set(v_result_3296_, 2, v_children_3288_);
v___x_3297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3297_, 0, v_priority_3295_);
lean_ctor_set(v___x_3297_, 1, v_result_3296_);
v___x_3298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
return v___x_3298_;
}
v___jp_3299_:
{
if (lean_obj_tag(v_info_3287_) == 2)
{
v___y_3291_ = v___y_3300_;
v___y_3292_ = v___y_3302_;
v___y_3293_ = v___y_3304_;
v___y_3294_ = v___y_3303_;
goto v___jp_3290_;
}
else
{
v___y_3291_ = v___y_3300_;
v___y_3292_ = v___y_3302_;
v___y_3293_ = v___y_3304_;
v___y_3294_ = v___y_3301_;
goto v___jp_3290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1___boxed(lean_object* v_filter_3341_, lean_object* v_hoverPos_3342_, lean_object* v_includeStop_3343_, lean_object* v_ctx_3344_, lean_object* v_info_3345_, lean_object* v_children_3346_, lean_object* v_results_3347_){
_start:
{
uint8_t v_includeStop_boxed_3348_; lean_object* v_res_3349_; 
v_includeStop_boxed_3348_ = lean_unbox(v_includeStop_3343_);
v_res_3349_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1(v_filter_3341_, v_hoverPos_3342_, v_includeStop_boxed_3348_, v_ctx_3344_, v_info_3345_, v_children_3346_, v_results_3347_);
lean_dec(v_hoverPos_3342_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(lean_object* v_t_3350_, lean_object* v_hoverPos_3351_, uint8_t v_includeStop_3352_, lean_object* v_filter_3353_){
_start:
{
lean_object* v___f_3354_; lean_object* v___x_3355_; lean_object* v_postNode_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___f_3354_ = ((lean_object*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___closed__0));
v___x_3355_ = lean_box(v_includeStop_3352_);
v_postNode_3356_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1___boxed), 7, 3);
lean_closure_set(v_postNode_3356_, 0, v_filter_3353_);
lean_closure_set(v_postNode_3356_, 1, v_hoverPos_3351_);
lean_closure_set(v_postNode_3356_, 2, v___x_3355_);
v___x_3357_ = lean_box(0);
v___x_3358_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v___f_3354_, v_postNode_3356_, v___x_3357_, v_t_3350_);
if (lean_obj_tag(v___x_3358_) == 0)
{
return v___x_3357_;
}
else
{
lean_object* v_val_3359_; 
v_val_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_val_3359_);
lean_dec_ref_known(v___x_3358_, 1);
if (lean_obj_tag(v_val_3359_) == 0)
{
return v___x_3357_;
}
else
{
lean_object* v_val_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3372_; 
v_val_3360_ = lean_ctor_get(v_val_3359_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v_val_3359_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3362_ = v_val_3359_;
v_isShared_3363_ = v_isSharedCheck_3372_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_val_3360_);
lean_dec(v_val_3359_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3372_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v_snd_3364_; lean_object* v_info_3365_; lean_object* v___x_3367_; 
v_snd_3364_ = lean_ctor_get(v_val_3360_, 1);
lean_inc(v_snd_3364_);
lean_dec(v_val_3360_);
v_info_3365_ = lean_ctor_get(v_snd_3364_, 1);
lean_inc_ref(v_info_3365_);
if (v_isShared_3363_ == 0)
{
lean_ctor_set(v___x_3362_, 0, v_snd_3364_);
v___x_3367_ = v___x_3362_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_snd_3364_);
v___x_3367_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
if (lean_obj_tag(v_info_3365_) == 1)
{
lean_object* v_i_3368_; lean_object* v_expr_3369_; uint8_t v___x_3370_; 
v_i_3368_ = lean_ctor_get(v_info_3365_, 0);
lean_inc_ref(v_i_3368_);
lean_dec_ref_known(v_info_3365_, 1);
v_expr_3369_ = lean_ctor_get(v_i_3368_, 3);
lean_inc_ref(v_expr_3369_);
lean_dec_ref(v_i_3368_);
v___x_3370_ = l_Lean_Expr_isSyntheticSorry(v_expr_3369_);
lean_dec_ref(v_expr_3369_);
if (v___x_3370_ == 0)
{
return v___x_3367_;
}
else
{
lean_dec_ref(v___x_3367_);
return v___x_3357_;
}
}
else
{
lean_dec_ref(v_info_3365_);
return v___x_3367_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___boxed(lean_object* v_t_3373_, lean_object* v_hoverPos_3374_, lean_object* v_includeStop_3375_, lean_object* v_filter_3376_){
_start:
{
uint8_t v_includeStop_boxed_3377_; lean_object* v_res_3378_; 
v_includeStop_boxed_3377_ = lean_unbox(v_includeStop_3375_);
v_res_3378_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(v_t_3373_, v_hoverPos_3374_, v_includeStop_boxed_3377_, v_filter_3376_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f(lean_object* v_t_3380_, lean_object* v_hoverPos_3381_){
_start:
{
lean_object* v_filter_3382_; uint8_t v___x_3383_; lean_object* v___x_3384_; 
v_filter_3382_ = ((lean_object*)(l_Lean_Elab_InfoTree_termGoalAt_x3f___closed__0));
v___x_3383_ = 1;
v___x_3384_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(v_t_3380_, v_hoverPos_3381_, v___x_3383_, v_filter_3382_);
return v___x_3384_;
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
