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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
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
lean_object* v_val_1147_; lean_object* v___x_1148_; 
v_val_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_val_1147_);
lean_dec_ref_known(v___x_1146_, 1);
v___x_1148_ = l_Lean_Elab_Info_tailPos_x3f(v_i_1144_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_dec(v_val_1147_);
return v___x_1148_;
}
else
{
lean_object* v_val_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1163_; 
v_val_1149_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1151_ = v___x_1148_;
v_isShared_1152_ = v_isSharedCheck_1163_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_val_1149_);
lean_dec(v___x_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1163_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
uint8_t v___x_1153_; 
v___x_1153_ = lean_nat_dec_le(v_val_1147_, v_hoverPos_1145_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; 
lean_del_object(v___x_1151_);
lean_dec(v_val_1149_);
lean_dec(v_val_1147_);
v___x_1154_ = lean_box(0);
return v___x_1154_;
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v___x_1155_ = lean_unsigned_to_nat(1u);
v___x_1156_ = lean_nat_add(v_hoverPos_1145_, v___x_1155_);
v___x_1157_ = lean_nat_dec_le(v___x_1156_, v_val_1149_);
lean_dec(v_val_1149_);
lean_dec(v___x_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; 
lean_del_object(v___x_1151_);
lean_dec(v_val_1147_);
v___x_1158_ = lean_box(0);
return v___x_1158_;
}
else
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = lean_nat_sub(v_hoverPos_1145_, v_val_1147_);
lean_dec(v_val_1147_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1159_);
v___x_1161_ = v___x_1151_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_occursInside_x3f___boxed(lean_object* v_i_1164_, lean_object* v_hoverPos_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_Elab_Info_occursInside_x3f(v_i_1164_, v_hoverPos_1165_);
lean_dec(v_hoverPos_1165_);
lean_dec_ref(v_i_1164_);
return v_res_1166_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Info_occursInOrOnBoundary(lean_object* v_i_1167_, lean_object* v_hoverPos_1168_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lean_Elab_Info_pos_x3f(v_i_1167_);
if (lean_obj_tag(v___x_1169_) == 1)
{
lean_object* v_val_1170_; lean_object* v___x_1171_; 
v_val_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_val_1170_);
lean_dec_ref_known(v___x_1169_, 1);
v___x_1171_ = l_Lean_Elab_Info_tailPos_x3f(v_i_1167_);
if (lean_obj_tag(v___x_1171_) == 1)
{
lean_object* v_val_1172_; uint8_t v___x_1173_; 
v_val_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_val_1172_);
lean_dec_ref_known(v___x_1171_, 1);
v___x_1173_ = lean_nat_dec_le(v_val_1170_, v_hoverPos_1168_);
lean_dec(v_val_1170_);
if (v___x_1173_ == 0)
{
lean_dec(v_val_1172_);
return v___x_1173_;
}
else
{
uint8_t v___x_1174_; 
v___x_1174_ = lean_nat_dec_le(v_hoverPos_1168_, v_val_1172_);
lean_dec(v_val_1172_);
return v___x_1174_;
}
}
else
{
uint8_t v___x_1175_; 
lean_dec(v___x_1171_);
lean_dec(v_val_1170_);
v___x_1175_ = 0;
return v___x_1175_;
}
}
else
{
uint8_t v___x_1176_; 
lean_dec(v___x_1169_);
v___x_1176_ = 0;
return v___x_1176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_occursInOrOnBoundary___boxed(lean_object* v_i_1177_, lean_object* v_hoverPos_1178_){
_start:
{
uint8_t v_res_1179_; lean_object* v_r_1180_; 
v_res_1179_ = l_Lean_Elab_Info_occursInOrOnBoundary(v_i_1177_, v_hoverPos_1178_);
lean_dec(v_hoverPos_1178_);
lean_dec_ref(v_i_1177_);
v_r_1180_ = lean_box(v_res_1179_);
return v_r_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0(lean_object* v_p_1181_, lean_object* v_ctx_1182_, lean_object* v_i_1183_, lean_object* v_x_1184_){
_start:
{
lean_object* v___x_1185_; uint8_t v___x_1186_; 
lean_inc_ref(v_i_1183_);
v___x_1185_ = lean_apply_1(v_p_1181_, v_i_1183_);
v___x_1186_ = lean_unbox(v___x_1185_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; 
lean_dec_ref(v_i_1183_);
lean_dec_ref(v_ctx_1182_);
v___x_1187_ = lean_box(0);
return v___x_1187_;
}
else
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1188_, 0, v_ctx_1182_);
lean_ctor_set(v___x_1188_, 1, v_i_1183_);
v___x_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0___boxed(lean_object* v_p_1190_, lean_object* v_ctx_1191_, lean_object* v_i_1192_, lean_object* v_x_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0(v_p_1190_, v_ctx_1191_, v_i_1192_, v_x_1193_);
lean_dec_ref(v_x_1193_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(lean_object* v_as_1195_, size_t v_i_1196_, size_t v_stop_1197_, lean_object* v_b_1198_){
_start:
{
lean_object* v___y_1200_; uint8_t v___x_1204_; 
v___x_1204_ = lean_usize_dec_eq(v_i_1196_, v_stop_1197_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v_fst_1206_; lean_object* v_fst_1207_; uint8_t v___x_1208_; 
v___x_1205_ = lean_array_uget_borrowed(v_as_1195_, v_i_1196_);
v_fst_1206_ = lean_ctor_get(v___x_1205_, 0);
v_fst_1207_ = lean_ctor_get(v_b_1198_, 0);
v___x_1208_ = lean_nat_dec_lt(v_fst_1206_, v_fst_1207_);
if (v___x_1208_ == 0)
{
v___y_1200_ = v_b_1198_;
goto v___jp_1199_;
}
else
{
v___y_1200_ = v___x_1205_;
goto v___jp_1199_;
}
}
else
{
lean_inc_ref(v_b_1198_);
return v_b_1198_;
}
v___jp_1199_:
{
size_t v___x_1201_; size_t v___x_1202_; 
v___x_1201_ = ((size_t)1ULL);
v___x_1202_ = lean_usize_add(v_i_1196_, v___x_1201_);
v_i_1196_ = v___x_1202_;
v_b_1198_ = v___y_1200_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1___boxed(lean_object* v_as_1209_, lean_object* v_i_1210_, lean_object* v_stop_1211_, lean_object* v_b_1212_){
_start:
{
size_t v_i_boxed_1213_; size_t v_stop_boxed_1214_; lean_object* v_res_1215_; 
v_i_boxed_1213_ = lean_unbox_usize(v_i_1210_);
lean_dec(v_i_1210_);
v_stop_boxed_1214_ = lean_unbox_usize(v_stop_1211_);
lean_dec(v_stop_1211_);
v_res_1215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(v_as_1209_, v_i_boxed_1213_, v_stop_boxed_1214_, v_b_1212_);
lean_dec_ref(v_b_1212_);
lean_dec_ref(v_as_1209_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1(lean_object* v_as_1216_){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1217_ = lean_unsigned_to_nat(0u);
v___x_1218_ = lean_array_get_size(v_as_1216_);
v___x_1219_ = lean_nat_dec_lt(v___x_1217_, v___x_1218_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_box(0);
return v___x_1220_;
}
else
{
lean_object* v_a0_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v_a0_1221_ = lean_array_fget_borrowed(v_as_1216_, v___x_1217_);
v___x_1222_ = lean_unsigned_to_nat(1u);
v___x_1223_ = lean_nat_dec_lt(v___x_1222_, v___x_1218_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; 
lean_inc(v_a0_1221_);
v___x_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1224_, 0, v_a0_1221_);
return v___x_1224_;
}
else
{
size_t v___x_1225_; size_t v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1225_ = ((size_t)1ULL);
v___x_1226_ = lean_usize_of_nat(v___x_1218_);
v___x_1227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(v_as_1216_, v___x_1225_, v___x_1226_, v_a0_1221_);
v___x_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1___boxed(lean_object* v_as_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1(v_as_1229_);
lean_dec_ref(v_as_1229_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__0(lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
if (lean_obj_tag(v_a_1231_) == 0)
{
lean_object* v___x_1233_; 
v___x_1233_ = lean_array_to_list(v_a_1232_);
return v___x_1233_;
}
else
{
lean_object* v_head_1234_; lean_object* v_tail_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1252_; 
v_head_1234_ = lean_ctor_get(v_a_1231_, 0);
v_tail_1235_ = lean_ctor_get(v_a_1231_, 1);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_a_1231_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1237_ = v_a_1231_;
v_isShared_1238_ = v_isSharedCheck_1252_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_tail_1235_);
lean_inc(v_head_1234_);
lean_dec(v_a_1231_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1252_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v_snd_1239_; lean_object* v___x_1240_; 
v_snd_1239_ = lean_ctor_get(v_head_1234_, 1);
v___x_1240_ = l_Lean_Elab_Info_pos_x3f(v_snd_1239_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_del_object(v___x_1237_);
lean_dec(v_head_1234_);
v_a_1231_ = v_tail_1235_;
goto _start;
}
else
{
lean_object* v_val_1242_; lean_object* v___x_1243_; 
v_val_1242_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_val_1242_);
lean_dec_ref_known(v___x_1240_, 1);
v___x_1243_ = l_Lean_Elab_Info_tailPos_x3f(v_snd_1239_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_dec(v_val_1242_);
lean_del_object(v___x_1237_);
lean_dec(v_head_1234_);
v_a_1231_ = v_tail_1235_;
goto _start;
}
else
{
lean_object* v_val_1245_; lean_object* v___x_1246_; lean_object* v___x_1248_; 
v_val_1245_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_val_1245_);
lean_dec_ref_known(v___x_1243_, 1);
v___x_1246_ = lean_nat_sub(v_val_1245_, v_val_1242_);
lean_dec(v_val_1242_);
lean_dec(v_val_1245_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set_tag(v___x_1237_, 0);
lean_ctor_set(v___x_1237_, 1, v_head_1234_);
lean_ctor_set(v___x_1237_, 0, v___x_1246_);
v___x_1248_ = v___x_1237_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_head_1234_);
v___x_1248_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_array_push(v_a_1232_, v___x_1248_);
v_a_1231_ = v_tail_1235_;
v_a_1232_ = v___x_1249_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f(lean_object* v_p_1255_, lean_object* v_t_1256_){
_start:
{
lean_object* v___f_1257_; lean_object* v_ts_1258_; lean_object* v___x_1259_; lean_object* v_infos_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___f_1257_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1257_, 0, v_p_1255_);
v_ts_1258_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_1257_, v_t_1256_);
v___x_1259_ = ((lean_object*)(l_Lean_Elab_InfoTree_smallestInfo_x3f___closed__0));
v_infos_1260_ = l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__0(v_ts_1258_, v___x_1259_);
v___x_1261_ = lean_array_mk(v_infos_1260_);
v___x_1262_ = l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1(v___x_1261_);
lean_dec_ref(v___x_1261_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v___x_1263_; 
v___x_1263_ = lean_box(0);
return v___x_1263_;
}
else
{
lean_object* v_val_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1272_; 
v_val_1264_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1266_ = v___x_1262_;
v_isShared_1267_ = v_isSharedCheck_1272_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_val_1264_);
lean_dec(v___x_1262_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1272_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v_snd_1268_; lean_object* v___x_1270_; 
v_snd_1268_ = lean_ctor_get(v_val_1264_, 1);
lean_inc(v_snd_1268_);
lean_dec(v_val_1264_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v_snd_1268_);
v___x_1270_ = v___x_1266_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_snd_1268_);
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
LEAN_EXPORT uint8_t l_Lean_Elab_instBEqHoverableInfoPrio_beq(lean_object* v_x_1273_, lean_object* v_x_1274_){
_start:
{
uint8_t v_isHoverPosOnStop_1275_; lean_object* v_size_1276_; uint8_t v_isVariableInfo_1277_; uint8_t v_isPartialTermInfo_1278_; uint8_t v_isHoverPosOnStop_1279_; lean_object* v_size_1280_; uint8_t v_isVariableInfo_1281_; uint8_t v_isPartialTermInfo_1282_; uint8_t v___y_1284_; 
v_isHoverPosOnStop_1275_ = lean_ctor_get_uint8(v_x_1273_, sizeof(void*)*1);
v_size_1276_ = lean_ctor_get(v_x_1273_, 0);
v_isVariableInfo_1277_ = lean_ctor_get_uint8(v_x_1273_, sizeof(void*)*1 + 1);
v_isPartialTermInfo_1278_ = lean_ctor_get_uint8(v_x_1273_, sizeof(void*)*1 + 2);
v_isHoverPosOnStop_1279_ = lean_ctor_get_uint8(v_x_1274_, sizeof(void*)*1);
v_size_1280_ = lean_ctor_get(v_x_1274_, 0);
v_isVariableInfo_1281_ = lean_ctor_get_uint8(v_x_1274_, sizeof(void*)*1 + 1);
v_isPartialTermInfo_1282_ = lean_ctor_get_uint8(v_x_1274_, sizeof(void*)*1 + 2);
if (v_isHoverPosOnStop_1279_ == 0)
{
if (v_isHoverPosOnStop_1275_ == 0)
{
goto v___jp_1285_;
}
else
{
return v_isHoverPosOnStop_1279_;
}
}
else
{
if (v_isHoverPosOnStop_1275_ == 0)
{
return v_isHoverPosOnStop_1275_;
}
else
{
goto v___jp_1285_;
}
}
v___jp_1283_:
{
if (v_isPartialTermInfo_1282_ == 0)
{
if (v_isPartialTermInfo_1278_ == 0)
{
return v___y_1284_;
}
else
{
return v_isPartialTermInfo_1282_;
}
}
else
{
return v_isPartialTermInfo_1278_;
}
}
v___jp_1285_:
{
uint8_t v___x_1286_; 
v___x_1286_ = lean_nat_dec_eq(v_size_1276_, v_size_1280_);
if (v___x_1286_ == 0)
{
return v___x_1286_;
}
else
{
if (v_isVariableInfo_1281_ == 0)
{
if (v_isVariableInfo_1277_ == 0)
{
v___y_1284_ = v___x_1286_;
goto v___jp_1283_;
}
else
{
return v_isVariableInfo_1281_;
}
}
else
{
if (v_isVariableInfo_1277_ == 0)
{
return v_isVariableInfo_1277_;
}
else
{
v___y_1284_ = v_isVariableInfo_1277_;
goto v___jp_1283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instBEqHoverableInfoPrio_beq___boxed(lean_object* v_x_1287_, lean_object* v_x_1288_){
_start:
{
uint8_t v_res_1289_; lean_object* v_r_1290_; 
v_res_1289_ = l_Lean_Elab_instBEqHoverableInfoPrio_beq(v_x_1287_, v_x_1288_);
lean_dec_ref(v_x_1288_);
lean_dec_ref(v_x_1287_);
v_r_1290_ = lean_box(v_res_1289_);
return v_r_1290_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(lean_object* v_i1_1293_, lean_object* v_i2_1294_){
_start:
{
uint8_t v_isHoverPosOnStop_1295_; lean_object* v_size_1296_; uint8_t v_isVariableInfo_1297_; uint8_t v_isPartialTermInfo_1298_; uint8_t v___y_1300_; uint8_t v___y_1321_; 
v_isHoverPosOnStop_1295_ = lean_ctor_get_uint8(v_i1_1293_, sizeof(void*)*1);
v_size_1296_ = lean_ctor_get(v_i1_1293_, 0);
v_isVariableInfo_1297_ = lean_ctor_get_uint8(v_i1_1293_, sizeof(void*)*1 + 1);
v_isPartialTermInfo_1298_ = lean_ctor_get_uint8(v_i1_1293_, sizeof(void*)*1 + 2);
if (v_isHoverPosOnStop_1295_ == 0)
{
v___y_1321_ = v_isHoverPosOnStop_1295_;
goto v___jp_1320_;
}
else
{
uint8_t v_isHoverPosOnStop_1322_; 
v_isHoverPosOnStop_1322_ = lean_ctor_get_uint8(v_i2_1294_, sizeof(void*)*1);
if (v_isHoverPosOnStop_1322_ == 0)
{
uint8_t v___x_1323_; 
v___x_1323_ = 0;
return v___x_1323_;
}
else
{
uint8_t v___x_1324_; 
v___x_1324_ = 0;
v___y_1321_ = v___x_1324_;
goto v___jp_1320_;
}
}
v___jp_1299_:
{
if (v_isPartialTermInfo_1298_ == 0)
{
uint8_t v_isPartialTermInfo_1301_; 
v_isPartialTermInfo_1301_ = lean_ctor_get_uint8(v_i2_1294_, sizeof(void*)*1 + 2);
if (v_isPartialTermInfo_1301_ == 0)
{
uint8_t v___x_1302_; 
v___x_1302_ = 1;
return v___x_1302_;
}
else
{
uint8_t v___x_1303_; 
v___x_1303_ = 2;
return v___x_1303_;
}
}
else
{
uint8_t v_isPartialTermInfo_1304_; 
v_isPartialTermInfo_1304_ = lean_ctor_get_uint8(v_i2_1294_, sizeof(void*)*1 + 2);
if (v_isPartialTermInfo_1304_ == 0)
{
uint8_t v___x_1305_; 
v___x_1305_ = 0;
return v___x_1305_;
}
else
{
if (v___y_1300_ == 0)
{
uint8_t v___x_1306_; 
v___x_1306_ = 1;
return v___x_1306_;
}
else
{
uint8_t v___x_1307_; 
v___x_1307_ = 0;
return v___x_1307_;
}
}
}
}
v___jp_1308_:
{
lean_object* v_size_1309_; uint8_t v_isVariableInfo_1310_; uint8_t v___x_1311_; 
v_size_1309_ = lean_ctor_get(v_i2_1294_, 0);
v_isVariableInfo_1310_ = lean_ctor_get_uint8(v_i2_1294_, sizeof(void*)*1 + 1);
v___x_1311_ = lean_nat_dec_lt(v_size_1309_, v_size_1296_);
if (v___x_1311_ == 0)
{
uint8_t v___x_1312_; 
v___x_1312_ = lean_nat_dec_lt(v_size_1296_, v_size_1309_);
if (v___x_1312_ == 0)
{
if (v_isVariableInfo_1297_ == 0)
{
if (v_isVariableInfo_1310_ == 0)
{
v___y_1300_ = v_isVariableInfo_1310_;
goto v___jp_1299_;
}
else
{
uint8_t v___x_1313_; 
v___x_1313_ = 2;
return v___x_1313_;
}
}
else
{
if (v_isVariableInfo_1310_ == 0)
{
uint8_t v___x_1314_; 
v___x_1314_ = 0;
return v___x_1314_;
}
else
{
v___y_1300_ = v___x_1312_;
goto v___jp_1299_;
}
}
}
else
{
uint8_t v___x_1315_; 
v___x_1315_ = 2;
return v___x_1315_;
}
}
else
{
uint8_t v___x_1316_; 
v___x_1316_ = 0;
return v___x_1316_;
}
}
v___jp_1317_:
{
uint8_t v_isHoverPosOnStop_1318_; 
v_isHoverPosOnStop_1318_ = lean_ctor_get_uint8(v_i2_1294_, sizeof(void*)*1);
if (v_isHoverPosOnStop_1318_ == 0)
{
goto v___jp_1308_;
}
else
{
uint8_t v___x_1319_; 
v___x_1319_ = 2;
return v___x_1319_;
}
}
v___jp_1320_:
{
if (v_isHoverPosOnStop_1295_ == 0)
{
goto v___jp_1317_;
}
else
{
if (v___y_1321_ == 0)
{
goto v___jp_1308_;
}
else
{
goto v___jp_1317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instOrdHoverableInfoPrio___lam__0___boxed(lean_object* v_i1_1325_, lean_object* v_i2_1326_){
_start:
{
uint8_t v_res_1327_; lean_object* v_r_1328_; 
v_res_1327_ = l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(v_i1_1325_, v_i2_1326_);
lean_dec_ref(v_i2_1326_);
lean_dec_ref(v_i1_1325_);
v_r_1328_ = lean_box(v_res_1327_);
return v_r_1328_;
}
}
static lean_object* _init_l_Lean_Elab_instLEHoverableInfoPrio(void){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = lean_box(0);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMaxHoverableInfoPrio___lam__0(lean_object* v_x_1332_, lean_object* v_y_1333_){
_start:
{
uint8_t v___x_1334_; 
v___x_1334_ = l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(v_x_1332_, v_y_1333_);
if (v___x_1334_ == 2)
{
lean_inc_ref(v_x_1332_);
return v_x_1332_;
}
else
{
lean_inc_ref(v_y_1333_);
return v_y_1333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMaxHoverableInfoPrio___lam__0___boxed(lean_object* v_x_1335_, lean_object* v_y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_Elab_instMaxHoverableInfoPrio___lam__0(v_x_1335_, v_y_1336_);
lean_dec_ref(v_y_1336_);
lean_dec_ref(v_x_1335_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0(lean_object* v_x_1340_){
_start:
{
lean_object* v_fst_1341_; 
v_fst_1341_ = lean_ctor_get(v_x_1340_, 0);
lean_inc(v_fst_1341_);
return v_fst_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0___boxed(lean_object* v_x_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0(v_x_1342_);
lean_dec_ref(v_x_1342_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1(lean_object* v_r_x3f_1344_){
_start:
{
if (lean_obj_tag(v_r_x3f_1344_) == 0)
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_box(0);
return v___x_1345_;
}
else
{
lean_object* v_val_1346_; 
v_val_1346_ = lean_ctor_get(v_r_x3f_1344_, 0);
lean_inc(v_val_1346_);
return v_val_1346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1___boxed(lean_object* v_r_x3f_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1(v_r_x3f_1347_);
lean_dec(v_r_x3f_1347_);
return v_res_1348_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2(lean_object* v___x_1349_, lean_object* v_maxPrio_x3f_1350_, lean_object* v_x_1351_){
_start:
{
lean_object* v_fst_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v_fst_1352_ = lean_ctor_get(v_x_1351_, 0);
lean_inc(v_fst_1352_);
v___x_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1353_, 0, v_fst_1352_);
v___x_1354_ = l_instBEqOption_beq___redArg(v___x_1349_, v___x_1353_, v_maxPrio_x3f_1350_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2___boxed(lean_object* v___x_1355_, lean_object* v_maxPrio_x3f_1356_, lean_object* v_x_1357_){
_start:
{
uint8_t v_res_1358_; lean_object* v_r_1359_; 
v_res_1358_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2(v___x_1355_, v_maxPrio_x3f_1356_, v_x_1357_);
lean_dec_ref(v_x_1357_);
v_r_1359_ = lean_box(v_res_1358_);
return v_r_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3(lean_object* v___f_1372_, lean_object* v___f_1373_, lean_object* v___x_1374_, lean_object* v_toPure_1375_, lean_object* v_info_1376_, lean_object* v_ctx_1377_, lean_object* v_children_1378_, lean_object* v_hoverPos_1379_, uint8_t v_includeStop_1380_, lean_object* v_results_1381_){
_start:
{
uint8_t v___y_1386_; uint8_t v___y_1387_; lean_object* v___y_1388_; uint8_t v___y_1389_; uint8_t v___y_1396_; uint8_t v___y_1397_; uint8_t v___y_1398_; lean_object* v___y_1399_; uint8_t v___y_1400_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v_maxPrio_x3f_1406_; lean_object* v___f_1407_; lean_object* v_bestResult_x3f_1408_; 
v___x_1404_ = lean_box(0);
lean_inc(v_results_1381_);
v___x_1405_ = l_List_mapTR_loop___redArg(v___f_1372_, v_results_1381_, v___x_1404_);
v_maxPrio_x3f_1406_ = l_List_max_x3f___redArg(v___f_1373_, v___x_1405_);
v___f_1407_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_1407_, 0, v___x_1374_);
lean_closure_set(v___f_1407_, 1, v_maxPrio_x3f_1406_);
v_bestResult_x3f_1408_ = l_List_find_x3f___redArg(v___f_1407_, v_results_1381_);
if (lean_obj_tag(v_bestResult_x3f_1408_) == 1)
{
lean_object* v___x_1409_; 
lean_dec_ref(v_children_1378_);
lean_dec_ref(v_ctx_1377_);
lean_dec_ref(v_info_1376_);
v___x_1409_ = lean_apply_2(v_toPure_1375_, lean_box(0), v_bestResult_x3f_1408_);
return v___x_1409_;
}
else
{
lean_object* v___x_1410_; uint8_t v___y_1412_; uint8_t v___y_1413_; uint8_t v___y_1414_; uint8_t v___y_1427_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
lean_dec(v_bestResult_x3f_1408_);
v___x_1410_ = l_Lean_Elab_Info_stx(v_info_1376_);
v___x_1430_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__1));
lean_inc(v___x_1410_);
v___x_1431_ = l_Lean_Syntax_isOfKind(v___x_1410_, v___x_1430_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; 
lean_inc_ref(v_info_1376_);
v___x_1432_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_1376_);
if (lean_obj_tag(v___x_1432_) == 0)
{
v___y_1427_ = v___x_1431_;
goto v___jp_1426_;
}
else
{
lean_object* v_val_1433_; lean_object* v_elaborator_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v_val_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_val_1433_);
lean_dec_ref_known(v___x_1432_, 1);
v_elaborator_1434_ = lean_ctor_get(v_val_1433_, 0);
lean_inc(v_elaborator_1434_);
lean_dec(v_val_1433_);
v___x_1435_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6));
v___x_1436_ = lean_name_eq(v_elaborator_1434_, v___x_1435_);
lean_dec(v_elaborator_1434_);
if (v___x_1436_ == 0)
{
v___y_1427_ = v___x_1436_;
goto v___jp_1426_;
}
else
{
lean_dec(v___x_1410_);
lean_dec_ref(v_children_1378_);
lean_dec_ref(v_ctx_1377_);
lean_dec_ref(v_info_1376_);
goto v___jp_1382_;
}
}
}
else
{
lean_dec(v___x_1410_);
lean_dec_ref(v_children_1378_);
lean_dec_ref(v_ctx_1377_);
lean_dec_ref(v_info_1376_);
goto v___jp_1382_;
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
v___x_1417_ = l_Lean_Syntax_Range_contains(v_val_1416_, v_hoverPos_1379_, v_includeStop_1380_);
if (v___x_1417_ == 0)
{
lean_dec(v_val_1416_);
lean_dec_ref(v_children_1378_);
lean_dec_ref(v_ctx_1377_);
lean_dec_ref(v_info_1376_);
goto v___jp_1401_;
}
else
{
if (v___y_1412_ == 0)
{
if (v___y_1414_ == 0)
{
lean_dec(v_val_1416_);
lean_dec_ref(v_children_1378_);
lean_dec_ref(v_ctx_1377_);
lean_dec_ref(v_info_1376_);
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
v_decide_1420_ = lean_nat_dec_eq(v_stop_1419_, v_hoverPos_1379_);
v___x_1421_ = lean_nat_sub(v_stop_1419_, v_start_1418_);
lean_dec(v_start_1418_);
lean_dec(v_stop_1419_);
if (lean_obj_tag(v_info_1376_) == 1)
{
lean_object* v_i_1422_; lean_object* v_expr_1423_; 
v_i_1422_ = lean_ctor_get(v_info_1376_, 0);
v_expr_1423_ = lean_ctor_get(v_i_1422_, 3);
if (lean_obj_tag(v_expr_1423_) == 1)
{
v___y_1396_ = v___y_1412_;
v___y_1397_ = v_decide_1420_;
v___y_1398_ = v___y_1413_;
v___y_1399_ = v___x_1421_;
v___y_1400_ = v___y_1413_;
goto v___jp_1395_;
}
else
{
v___y_1396_ = v___y_1412_;
v___y_1397_ = v_decide_1420_;
v___y_1398_ = v___y_1413_;
v___y_1399_ = v___x_1421_;
v___y_1400_ = v___y_1412_;
goto v___jp_1395_;
}
}
else
{
v___y_1396_ = v___y_1412_;
v___y_1397_ = v_decide_1420_;
v___y_1398_ = v___y_1413_;
v___y_1399_ = v___x_1421_;
v___y_1400_ = v___y_1412_;
goto v___jp_1395_;
}
}
}
else
{
lean_dec(v_val_1416_);
lean_dec_ref(v_children_1378_);
lean_dec_ref(v_ctx_1377_);
lean_dec_ref(v_info_1376_);
goto v___jp_1401_;
}
}
}
else
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
lean_dec(v___x_1415_);
lean_dec_ref(v_children_1378_);
lean_dec_ref(v_ctx_1377_);
lean_dec_ref(v_info_1376_);
v___x_1424_ = lean_box(0);
v___x_1425_ = lean_apply_2(v_toPure_1375_, lean_box(0), v___x_1424_);
return v___x_1425_;
}
}
v___jp_1426_:
{
uint8_t v___x_1428_; 
v___x_1428_ = 1;
switch(lean_obj_tag(v_info_1376_))
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
if (v___y_1427_ == 0)
{
lean_object* v___x_1429_; 
lean_inc_ref(v_info_1376_);
v___x_1429_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_1376_);
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
else
{
v___y_1412_ = v___y_1427_;
v___y_1413_ = v___x_1428_;
v___y_1414_ = v___y_1427_;
goto v___jp_1411_;
}
}
}
}
}
v___jp_1382_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = lean_box(0);
v___x_1384_ = lean_apply_2(v_toPure_1375_, lean_box(0), v___x_1383_);
return v___x_1384_;
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
lean_ctor_set(v_result_1391_, 0, v_ctx_1377_);
lean_ctor_set(v_result_1391_, 1, v_info_1376_);
lean_ctor_set(v_result_1391_, 2, v_children_1378_);
v___x_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1392_, 0, v_priority_1390_);
lean_ctor_set(v___x_1392_, 1, v_result_1391_);
v___x_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
v___x_1394_ = lean_apply_2(v_toPure_1375_, lean_box(0), v___x_1393_);
return v___x_1394_;
}
v___jp_1395_:
{
if (lean_obj_tag(v_info_1376_) == 2)
{
v___y_1386_ = v___y_1397_;
v___y_1387_ = v___y_1400_;
v___y_1388_ = v___y_1399_;
v___y_1389_ = v___y_1398_;
goto v___jp_1385_;
}
else
{
v___y_1386_ = v___y_1397_;
v___y_1387_ = v___y_1400_;
v___y_1388_ = v___y_1399_;
v___y_1389_ = v___y_1396_;
goto v___jp_1385_;
}
}
v___jp_1401_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = lean_box(0);
v___x_1403_ = lean_apply_2(v_toPure_1375_, lean_box(0), v___x_1402_);
return v___x_1403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___boxed(lean_object* v___f_1437_, lean_object* v___f_1438_, lean_object* v___x_1439_, lean_object* v_toPure_1440_, lean_object* v_info_1441_, lean_object* v_ctx_1442_, lean_object* v_children_1443_, lean_object* v_hoverPos_1444_, lean_object* v_includeStop_1445_, lean_object* v_results_1446_){
_start:
{
uint8_t v_includeStop_boxed_1447_; lean_object* v_res_1448_; 
v_includeStop_boxed_1447_ = lean_unbox(v_includeStop_1445_);
v_res_1448_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3(v___f_1437_, v___f_1438_, v___x_1439_, v_toPure_1440_, v_info_1441_, v_ctx_1442_, v_children_1443_, v_hoverPos_1444_, v_includeStop_boxed_1447_, v_results_1446_);
lean_dec(v_hoverPos_1444_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4(lean_object* v___f_1451_, lean_object* v___f_1452_, lean_object* v___x_1453_, lean_object* v_toPure_1454_, lean_object* v_hoverPos_1455_, uint8_t v_includeStop_1456_, lean_object* v___f_1457_, lean_object* v_filter_1458_, lean_object* v_toBind_1459_, lean_object* v_ctx_1460_, lean_object* v_info_1461_, lean_object* v_children_1462_, lean_object* v_results_1463_){
_start:
{
lean_object* v___x_1464_; lean_object* v___f_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1464_ = lean_box(v_includeStop_1456_);
lean_inc_ref(v_children_1462_);
lean_inc_ref(v_ctx_1460_);
lean_inc_ref(v_info_1461_);
v___f_1465_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_1465_, 0, v___f_1451_);
lean_closure_set(v___f_1465_, 1, v___f_1452_);
lean_closure_set(v___f_1465_, 2, v___x_1453_);
lean_closure_set(v___f_1465_, 3, v_toPure_1454_);
lean_closure_set(v___f_1465_, 4, v_info_1461_);
lean_closure_set(v___f_1465_, 5, v_ctx_1460_);
lean_closure_set(v___f_1465_, 6, v_children_1462_);
lean_closure_set(v___f_1465_, 7, v_hoverPos_1455_);
lean_closure_set(v___f_1465_, 8, v___x_1464_);
v___x_1466_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___closed__0));
v___x_1467_ = l_List_filterMapTR_go___redArg(v___f_1457_, v_results_1463_, v___x_1466_);
v___x_1468_ = lean_apply_4(v_filter_1458_, v_ctx_1460_, v_info_1461_, v_children_1462_, v___x_1467_);
v___x_1469_ = lean_apply_4(v_toBind_1459_, lean_box(0), lean_box(0), v___x_1468_, v___f_1465_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___boxed(lean_object* v___f_1470_, lean_object* v___f_1471_, lean_object* v___x_1472_, lean_object* v_toPure_1473_, lean_object* v_hoverPos_1474_, lean_object* v_includeStop_1475_, lean_object* v___f_1476_, lean_object* v_filter_1477_, lean_object* v_toBind_1478_, lean_object* v_ctx_1479_, lean_object* v_info_1480_, lean_object* v_children_1481_, lean_object* v_results_1482_){
_start:
{
uint8_t v_includeStop_boxed_1483_; lean_object* v_res_1484_; 
v_includeStop_boxed_1483_ = lean_unbox(v_includeStop_1475_);
v_res_1484_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4(v___f_1470_, v___f_1471_, v___x_1472_, v_toPure_1473_, v_hoverPos_1474_, v_includeStop_boxed_1483_, v___f_1476_, v_filter_1477_, v_toBind_1478_, v_ctx_1479_, v_info_1480_, v_children_1481_, v_results_1482_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__6(lean_object* v_toPure_1485_, lean_object* v_results_1486_){
_start:
{
if (lean_obj_tag(v_results_1486_) == 0)
{
goto v___jp_1487_;
}
else
{
lean_object* v_val_1490_; 
v_val_1490_ = lean_ctor_get(v_results_1486_, 0);
lean_inc(v_val_1490_);
lean_dec_ref_known(v_results_1486_, 1);
if (lean_obj_tag(v_val_1490_) == 0)
{
goto v___jp_1487_;
}
else
{
lean_object* v_val_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1507_; 
v_val_1491_ = lean_ctor_get(v_val_1490_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_val_1490_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1493_ = v_val_1490_;
v_isShared_1494_ = v_isSharedCheck_1507_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_val_1491_);
lean_dec(v_val_1490_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1507_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v_snd_1495_; lean_object* v_info_1496_; lean_object* v___x_1498_; 
v_snd_1495_ = lean_ctor_get(v_val_1491_, 1);
lean_inc(v_snd_1495_);
lean_dec(v_val_1491_);
v_info_1496_ = lean_ctor_get(v_snd_1495_, 1);
lean_inc_ref(v_info_1496_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v_snd_1495_);
v___x_1498_ = v___x_1493_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_snd_1495_);
v___x_1498_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
if (lean_obj_tag(v_info_1496_) == 1)
{
lean_object* v_i_1499_; lean_object* v_expr_1500_; uint8_t v___x_1501_; 
v_i_1499_ = lean_ctor_get(v_info_1496_, 0);
lean_inc_ref(v_i_1499_);
lean_dec_ref_known(v_info_1496_, 1);
v_expr_1500_ = lean_ctor_get(v_i_1499_, 3);
lean_inc_ref(v_expr_1500_);
lean_dec_ref(v_i_1499_);
v___x_1501_ = l_Lean_Expr_isSyntheticSorry(v_expr_1500_);
lean_dec_ref(v_expr_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_apply_2(v_toPure_1485_, lean_box(0), v___x_1498_);
return v___x_1502_;
}
else
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_dec_ref(v___x_1498_);
v___x_1503_ = lean_box(0);
v___x_1504_ = lean_apply_2(v_toPure_1485_, lean_box(0), v___x_1503_);
return v___x_1504_;
}
}
else
{
lean_object* v___x_1505_; 
lean_dec_ref(v_info_1496_);
v___x_1505_ = lean_apply_2(v_toPure_1485_, lean_box(0), v___x_1498_);
return v___x_1505_;
}
}
}
}
}
v___jp_1487_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_box(0);
v___x_1489_ = lean_apply_2(v_toPure_1485_, lean_box(0), v___x_1488_);
return v___x_1489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg(lean_object* v_inst_1510_, lean_object* v_t_1511_, lean_object* v_hoverPos_1512_, uint8_t v_includeStop_1513_, lean_object* v_filter_1514_){
_start:
{
lean_object* v_toApplicative_1515_; lean_object* v_toBind_1516_; lean_object* v_toPure_1517_; lean_object* v___f_1518_; lean_object* v___f_1519_; lean_object* v___f_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v_postNode_1523_; lean_object* v___f_1524_; lean_object* v___f_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v_toApplicative_1515_ = lean_ctor_get(v_inst_1510_, 0);
v_toBind_1516_ = lean_ctor_get(v_inst_1510_, 1);
lean_inc_n(v_toBind_1516_, 2);
v_toPure_1517_ = lean_ctor_get(v_toApplicative_1515_, 1);
v___f_1518_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__0));
v___f_1519_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__1));
v___f_1520_ = ((lean_object*)(l_Lean_Elab_instMaxHoverableInfoPrio___closed__0));
v___x_1521_ = ((lean_object*)(l_Lean_Elab_instBEqHoverableInfoPrio___closed__0));
v___x_1522_ = lean_box(v_includeStop_1513_);
lean_inc_n(v_toPure_1517_, 3);
v_postNode_1523_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___boxed), 13, 9);
lean_closure_set(v_postNode_1523_, 0, v___f_1518_);
lean_closure_set(v_postNode_1523_, 1, v___f_1520_);
lean_closure_set(v_postNode_1523_, 2, v___x_1521_);
lean_closure_set(v_postNode_1523_, 3, v_toPure_1517_);
lean_closure_set(v_postNode_1523_, 4, v_hoverPos_1512_);
lean_closure_set(v_postNode_1523_, 5, v___x_1522_);
lean_closure_set(v_postNode_1523_, 6, v___f_1519_);
lean_closure_set(v_postNode_1523_, 7, v_filter_1514_);
lean_closure_set(v_postNode_1523_, 8, v_toBind_1516_);
v___f_1524_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__2___boxed), 4, 1);
lean_closure_set(v___f_1524_, 0, v_toPure_1517_);
v___f_1525_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__6), 2, 1);
lean_closure_set(v___f_1525_, 0, v_toPure_1517_);
v___x_1526_ = lean_box(0);
v___x_1527_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_1510_, v___f_1524_, v_postNode_1523_, v___x_1526_, v_t_1511_);
v___x_1528_ = lean_apply_4(v_toBind_1516_, lean_box(0), lean_box(0), v___x_1527_, v___f_1525_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___boxed(lean_object* v_inst_1529_, lean_object* v_t_1530_, lean_object* v_hoverPos_1531_, lean_object* v_includeStop_1532_, lean_object* v_filter_1533_){
_start:
{
uint8_t v_includeStop_boxed_1534_; lean_object* v_res_1535_; 
v_includeStop_boxed_1534_ = lean_unbox(v_includeStop_1532_);
v_res_1535_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg(v_inst_1529_, v_t_1530_, v_hoverPos_1531_, v_includeStop_boxed_1534_, v_filter_1533_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f(lean_object* v_m_1536_, lean_object* v_inst_1537_, lean_object* v_t_1538_, lean_object* v_hoverPos_1539_, uint8_t v_includeStop_1540_, lean_object* v_filter_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg(v_inst_1537_, v_t_1538_, v_hoverPos_1539_, v_includeStop_1540_, v_filter_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___boxed(lean_object* v_m_1543_, lean_object* v_inst_1544_, lean_object* v_t_1545_, lean_object* v_hoverPos_1546_, lean_object* v_includeStop_1547_, lean_object* v_filter_1548_){
_start:
{
uint8_t v_includeStop_boxed_1549_; lean_object* v_res_1550_; 
v_includeStop_boxed_1549_ = lean_unbox(v_includeStop_1547_);
v_res_1550_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f(v_m_1543_, v_inst_1544_, v_t_1545_, v_hoverPos_1546_, v_includeStop_boxed_1549_, v_filter_1548_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_type_x3f(lean_object* v_i_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
switch(lean_obj_tag(v_i_1551_))
{
case 1:
{
lean_object* v_i_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1582_; 
v_i_1557_ = lean_ctor_get(v_i_1551_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_i_1551_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1559_ = v_i_1551_;
v_isShared_1560_ = v_isSharedCheck_1582_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_i_1557_);
lean_dec(v_i_1551_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1582_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v_expr_1561_; lean_object* v___x_1562_; 
v_expr_1561_ = lean_ctor_get(v_i_1557_, 3);
lean_inc_ref(v_expr_1561_);
lean_dec_ref(v_i_1557_);
lean_inc(v_a_1555_);
lean_inc_ref(v_a_1554_);
lean_inc(v_a_1553_);
lean_inc_ref(v_a_1552_);
v___x_1562_ = lean_infer_type(v_expr_1561_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1573_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1573_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1573_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v_a_1563_);
v___x_1568_ = v___x_1559_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v___x_1570_; 
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v___x_1568_);
v___x_1570_ = v___x_1565_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_del_object(v___x_1559_);
v_a_1574_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1562_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1562_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
case 7:
{
lean_object* v_i_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1608_; 
v_i_1583_ = lean_ctor_get(v_i_1551_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_i_1551_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1585_ = v_i_1551_;
v_isShared_1586_ = v_isSharedCheck_1608_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_i_1583_);
lean_dec(v_i_1551_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1608_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v_val_1587_; lean_object* v___x_1588_; 
v_val_1587_ = lean_ctor_get(v_i_1583_, 3);
lean_inc_ref(v_val_1587_);
lean_dec_ref(v_i_1583_);
lean_inc(v_a_1555_);
lean_inc_ref(v_a_1554_);
lean_inc(v_a_1553_);
lean_inc_ref(v_a_1552_);
v___x_1588_ = lean_infer_type(v_val_1587_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1599_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1599_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1599_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1586_ == 0)
{
lean_ctor_set_tag(v___x_1585_, 1);
lean_ctor_set(v___x_1585_, 0, v_a_1589_);
v___x_1594_ = v___x_1585_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v___x_1596_; 
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1594_);
v___x_1596_ = v___x_1591_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_del_object(v___x_1585_);
v_a_1600_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1588_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1588_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
case 13:
{
lean_object* v_i_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1635_; 
v_i_1609_ = lean_ctor_get(v_i_1551_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_i_1551_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1611_ = v_i_1551_;
v_isShared_1612_ = v_isSharedCheck_1635_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_i_1609_);
lean_dec(v_i_1551_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1635_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v_toTermInfo_1613_; lean_object* v_expr_1614_; lean_object* v___x_1615_; 
v_toTermInfo_1613_ = lean_ctor_get(v_i_1609_, 0);
lean_inc_ref(v_toTermInfo_1613_);
lean_dec_ref(v_i_1609_);
v_expr_1614_ = lean_ctor_get(v_toTermInfo_1613_, 3);
lean_inc_ref(v_expr_1614_);
lean_dec_ref(v_toTermInfo_1613_);
lean_inc(v_a_1555_);
lean_inc_ref(v_a_1554_);
lean_inc(v_a_1553_);
lean_inc_ref(v_a_1552_);
v___x_1615_ = lean_infer_type(v_expr_1614_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1626_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1626_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1626_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1612_ == 0)
{
lean_ctor_set_tag(v___x_1611_, 1);
lean_ctor_set(v___x_1611_, 0, v_a_1616_);
v___x_1621_ = v___x_1611_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1623_; 
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v___x_1621_);
v___x_1623_ = v___x_1618_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_del_object(v___x_1611_);
v_a_1627_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1615_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1615_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
default: 
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_dec_ref(v_i_1551_);
v___x_1636_ = lean_box(0);
v___x_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
return v___x_1637_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_type_x3f___boxed(lean_object* v_i_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lean_Elab_Info_type_x3f(v_i_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_);
lean_dec(v_a_1642_);
lean_dec_ref(v_a_1641_);
lean_dec(v_a_1640_);
lean_dec_ref(v_a_1639_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(lean_object* v_declName_1645_, uint8_t v_includeBuiltin_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v___x_1650_; lean_object* v_toCold_1651_; lean_object* v_env_1652_; lean_object* v_ref_1653_; lean_object* v_currNamespace_1654_; lean_object* v_openDecls_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1650_ = lean_st_ref_get(v___y_1648_);
v_toCold_1651_ = lean_ctor_get(v___y_1647_, 0);
v_env_1652_ = lean_ctor_get(v___x_1650_, 0);
lean_inc_ref(v_env_1652_);
lean_dec(v___x_1650_);
v_ref_1653_ = lean_ctor_get(v___y_1647_, 2);
v_currNamespace_1654_ = lean_ctor_get(v_toCold_1651_, 4);
v_openDecls_1655_ = lean_ctor_get(v_toCold_1651_, 5);
v___x_1656_ = l_Lean_Options_empty;
lean_inc(v_openDecls_1655_);
lean_inc(v_currNamespace_1654_);
v___x_1657_ = l_Lean_findDocString_x3f(v_env_1652_, v_declName_1645_, v_includeBuiltin_1646_, v___x_1656_, v_currNamespace_1654_, v_openDecls_1655_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1677_; 
v_a_1666_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1668_ = v___x_1657_;
v_isShared_1669_ = v_isSharedCheck_1677_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1657_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1677_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1670_ = lean_io_error_to_string(v_a_1666_);
v___x_1671_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
v___x_1672_ = l_Lean_MessageData_ofFormat(v___x_1671_);
lean_inc(v_ref_1653_);
v___x_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1673_, 0, v_ref_1653_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v___x_1673_);
v___x_1675_ = v___x_1668_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg___boxed(lean_object* v_declName_1678_, lean_object* v_includeBuiltin_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
uint8_t v_includeBuiltin_boxed_1683_; lean_object* v_res_1684_; 
v_includeBuiltin_boxed_1683_ = lean_unbox(v_includeBuiltin_1679_);
v_res_1684_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_declName_1678_, v_includeBuiltin_boxed_1683_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0(lean_object* v_declName_1685_, uint8_t v_includeBuiltin_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_declName_1685_, v_includeBuiltin_1686_, v___y_1689_, v___y_1690_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___boxed(lean_object* v_declName_1693_, lean_object* v_includeBuiltin_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
uint8_t v_includeBuiltin_boxed_1700_; lean_object* v_res_1701_; 
v_includeBuiltin_boxed_1700_ = lean_unbox(v_includeBuiltin_1694_);
v_res_1701_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0(v_declName_1693_, v_includeBuiltin_boxed_1700_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg(lean_object* v_name_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v_env_1707_; lean_object* v___x_1708_; lean_object* v_toEnvExtension_1709_; lean_object* v_asyncMode_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1705_ = lean_box(1);
v___x_1706_ = lean_st_ref_get(v___y_1703_);
v_env_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc_ref(v_env_1707_);
lean_dec(v___x_1706_);
v___x_1708_ = l_Lean_errorExplanationExt;
v_toEnvExtension_1709_ = lean_ctor_get(v___x_1708_, 0);
v_asyncMode_1710_ = lean_ctor_get(v_toEnvExtension_1709_, 2);
v___x_1711_ = lean_box(0);
v___x_1712_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1705_, v___x_1708_, v_env_1707_, v_asyncMode_1710_, v___x_1711_);
v___x_1713_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1712_, v_name_1702_);
lean_dec(v___x_1712_);
v___x_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg___boxed(lean_object* v_name_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg(v_name_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec(v_name_1715_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1(lean_object* v_name_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg(v_name_1719_, v___y_1723_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___boxed(lean_object* v_name_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1(v_name_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v_name_1726_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_docString_x3f(lean_object* v_i_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; 
switch(lean_obj_tag(v_i_1733_))
{
case 1:
{
lean_object* v_i_1755_; lean_object* v_expr_1756_; lean_object* v___x_1757_; 
v_i_1755_ = lean_ctor_get(v_i_1733_, 0);
v_expr_1756_ = lean_ctor_get(v_i_1755_, 3);
v___x_1757_ = l_Lean_Expr_constName_x3f(v_expr_1756_);
if (lean_obj_tag(v___x_1757_) == 1)
{
lean_object* v_val_1758_; uint8_t v___x_1759_; lean_object* v___x_1760_; 
lean_dec_ref_known(v_i_1733_, 1);
v_val_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_val_1758_);
lean_dec_ref_known(v___x_1757_, 1);
v___x_1759_ = 1;
v___x_1760_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_val_1758_, v___x_1759_, v_a_1736_, v_a_1737_);
return v___x_1760_;
}
else
{
lean_dec(v___x_1757_);
v___y_1740_ = v_a_1734_;
v___y_1741_ = v_a_1735_;
v___y_1742_ = v_a_1736_;
v___y_1743_ = v_a_1737_;
goto v___jp_1739_;
}
}
case 13:
{
lean_object* v_i_1761_; lean_object* v___x_1762_; 
v_i_1761_ = lean_ctor_get(v_i_1733_, 0);
v___x_1762_ = l_Lean_Meta_getPPContext(v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v_ref_1764_; lean_object* v___x_1765_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
v_ref_1764_ = lean_ctor_get(v_a_1736_, 2);
lean_inc_ref(v_i_1761_);
v___x_1765_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v_a_1763_, v_i_1761_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1779_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1779_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1779_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
if (lean_obj_tag(v_a_1766_) == 1)
{
lean_object* v___x_1771_; 
lean_dec_ref_known(v_i_1733_, 1);
if (v_isShared_1769_ == 0)
{
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1766_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
else
{
lean_object* v_toTermInfo_1773_; lean_object* v_expr_1774_; lean_object* v___x_1775_; 
lean_del_object(v___x_1768_);
lean_dec(v_a_1766_);
v_toTermInfo_1773_ = lean_ctor_get(v_i_1761_, 0);
v_expr_1774_ = lean_ctor_get(v_toTermInfo_1773_, 3);
v___x_1775_ = l_Lean_Expr_constName_x3f(v_expr_1774_);
if (lean_obj_tag(v___x_1775_) == 1)
{
lean_object* v_val_1776_; uint8_t v___x_1777_; lean_object* v___x_1778_; 
lean_dec_ref_known(v_i_1733_, 1);
v_val_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_val_1776_);
lean_dec_ref_known(v___x_1775_, 1);
v___x_1777_ = 1;
v___x_1778_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_val_1776_, v___x_1777_, v_a_1736_, v_a_1737_);
return v___x_1778_;
}
else
{
lean_dec(v___x_1775_);
v___y_1740_ = v_a_1734_;
v___y_1741_ = v_a_1735_;
v___y_1742_ = v_a_1736_;
v___y_1743_ = v_a_1737_;
goto v___jp_1739_;
}
}
}
}
else
{
lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1797_; 
v_isSharedCheck_1797_ = !lean_is_exclusive(v_i_1733_);
if (v_isSharedCheck_1797_ == 0)
{
lean_object* v_unused_1798_; 
v_unused_1798_ = lean_ctor_get(v_i_1733_, 0);
lean_dec(v_unused_1798_);
v___x_1781_ = v_i_1733_;
v_isShared_1782_ = v_isSharedCheck_1797_;
goto v_resetjp_1780_;
}
else
{
lean_dec(v_i_1733_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1797_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1796_; 
v_a_1783_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1785_ = v___x_1765_;
v_isShared_1786_ = v_isSharedCheck_1796_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1765_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1796_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1787_; lean_object* v___x_1789_; 
v___x_1787_ = lean_io_error_to_string(v_a_1783_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set_tag(v___x_1781_, 3);
lean_ctor_set(v___x_1781_, 0, v___x_1787_);
v___x_1789_ = v___x_1781_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1790_ = l_Lean_MessageData_ofFormat(v___x_1789_);
lean_inc(v_ref_1764_);
v___x_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1791_, 0, v_ref_1764_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v___x_1791_);
v___x_1793_ = v___x_1785_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec_ref_known(v_i_1733_, 1);
v_a_1799_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1762_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1762_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
case 7:
{
lean_object* v_i_1807_; lean_object* v_projName_1808_; uint8_t v___x_1809_; lean_object* v___x_1810_; 
v_i_1807_ = lean_ctor_get(v_i_1733_, 0);
lean_inc_ref(v_i_1807_);
lean_dec_ref_known(v_i_1733_, 1);
v_projName_1808_ = lean_ctor_get(v_i_1807_, 0);
lean_inc(v_projName_1808_);
lean_dec_ref(v_i_1807_);
v___x_1809_ = 1;
v___x_1810_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_projName_1808_, v___x_1809_, v_a_1736_, v_a_1737_);
return v___x_1810_;
}
case 5:
{
lean_object* v_i_1811_; lean_object* v_optionName_1812_; lean_object* v_declName_1813_; uint8_t v___x_1814_; lean_object* v___x_1815_; 
v_i_1811_ = lean_ctor_get(v_i_1733_, 0);
lean_inc_ref(v_i_1811_);
lean_dec_ref_known(v_i_1733_, 1);
v_optionName_1812_ = lean_ctor_get(v_i_1811_, 1);
lean_inc(v_optionName_1812_);
v_declName_1813_ = lean_ctor_get(v_i_1811_, 2);
lean_inc(v_declName_1813_);
lean_dec_ref(v_i_1811_);
v___x_1814_ = 1;
v___x_1815_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_declName_1813_, v___x_1814_, v_a_1736_, v_a_1737_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
if (lean_obj_tag(v_a_1816_) == 1)
{
lean_dec(v_optionName_1812_);
return v___x_1815_;
}
else
{
lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1858_; 
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1858_ == 0)
{
lean_object* v_unused_1859_; 
v_unused_1859_ = lean_ctor_get(v___x_1815_, 0);
lean_dec(v_unused_1859_);
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1858_;
goto v_resetjp_1817_;
}
else
{
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1858_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v_ref_1820_; lean_object* v___x_1821_; 
v_ref_1820_ = lean_ctor_get(v_a_1736_, 2);
v___x_1821_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1843_; 
lean_del_object(v___x_1818_);
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1843_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1843_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1822_, v_optionName_1812_);
lean_dec(v_optionName_1812_);
lean_dec(v_a_1822_);
if (lean_obj_tag(v___x_1826_) == 1)
{
lean_object* v_val_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1838_; 
v_val_1827_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1829_ = v___x_1826_;
v_isShared_1830_ = v_isSharedCheck_1838_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_val_1827_);
lean_dec(v___x_1826_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1838_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1831_ = l_Lean_OptionDecl_fullDescr(v_val_1827_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1831_);
v___x_1833_ = v___x_1829_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
lean_object* v___x_1835_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1833_);
v___x_1835_ = v___x_1824_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
else
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
lean_dec(v___x_1826_);
v___x_1839_ = lean_box(0);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1839_);
v___x_1841_ = v___x_1824_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1857_; 
lean_dec(v_optionName_1812_);
v_a_1844_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1846_ = v___x_1821_;
v_isShared_1847_ = v_isSharedCheck_1857_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1821_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1857_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1848_ = lean_io_error_to_string(v_a_1844_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set_tag(v___x_1818_, 3);
lean_ctor_set(v___x_1818_, 0, v___x_1848_);
v___x_1850_ = v___x_1818_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1851_ = l_Lean_MessageData_ofFormat(v___x_1850_);
lean_inc(v_ref_1820_);
v___x_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1852_, 0, v_ref_1820_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1852_);
v___x_1854_ = v___x_1846_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
}
}
else
{
lean_dec(v_optionName_1812_);
return v___x_1815_;
}
}
case 6:
{
lean_object* v_i_1860_; lean_object* v_errorName_1861_; lean_object* v___x_1862_; lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1883_; 
v_i_1860_ = lean_ctor_get(v_i_1733_, 0);
lean_inc_ref(v_i_1860_);
lean_dec_ref_known(v_i_1733_, 1);
v_errorName_1861_ = lean_ctor_get(v_i_1860_, 1);
lean_inc(v_errorName_1861_);
lean_dec_ref(v_i_1860_);
v___x_1862_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg(v_errorName_1861_, v_a_1737_);
lean_dec(v_errorName_1861_);
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1865_ = v___x_1862_;
v_isShared_1866_ = v_isSharedCheck_1883_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1862_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1883_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
if (lean_obj_tag(v_a_1863_) == 1)
{
lean_object* v_val_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1878_; 
v_val_1867_ = lean_ctor_get(v_a_1863_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_a_1863_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1869_ = v_a_1863_;
v_isShared_1870_ = v_isSharedCheck_1878_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_val_1867_);
lean_dec(v_a_1863_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1878_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; lean_object* v___x_1873_; 
v___x_1871_ = l_Lean_ErrorExplanation_summaryWithSeverity(v_val_1867_);
lean_dec(v_val_1867_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v___x_1871_);
v___x_1873_ = v___x_1869_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1871_);
v___x_1873_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v___x_1875_; 
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1873_);
v___x_1875_ = v___x_1865_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v___x_1879_; lean_object* v___x_1881_; 
lean_dec(v_a_1863_);
v___x_1879_ = lean_box(0);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1879_);
v___x_1881_ = v___x_1865_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
case 16:
{
lean_object* v_i_1884_; lean_object* v_stx_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; lean_object* v___x_1888_; 
v_i_1884_ = lean_ctor_get(v_i_1733_, 0);
lean_inc_ref(v_i_1884_);
lean_dec_ref_known(v_i_1733_, 1);
v_stx_1885_ = lean_ctor_get(v_i_1884_, 1);
lean_inc(v_stx_1885_);
lean_dec_ref(v_i_1884_);
v___x_1886_ = l_Lean_Syntax_getKind(v_stx_1885_);
v___x_1887_ = 1;
v___x_1888_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v___x_1886_, v___x_1887_, v_a_1736_, v_a_1737_);
return v___x_1888_;
}
case 17:
{
lean_object* v_i_1889_; lean_object* v_name_1890_; uint8_t v___x_1891_; lean_object* v___x_1892_; 
v_i_1889_ = lean_ctor_get(v_i_1733_, 0);
lean_inc_ref(v_i_1889_);
lean_dec_ref_known(v_i_1733_, 1);
v_name_1890_ = lean_ctor_get(v_i_1889_, 1);
lean_inc(v_name_1890_);
lean_dec_ref(v_i_1889_);
v___x_1891_ = 1;
v___x_1892_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_name_1890_, v___x_1891_, v_a_1736_, v_a_1737_);
return v___x_1892_;
}
default: 
{
v___y_1740_ = v_a_1734_;
v___y_1741_ = v_a_1735_;
v___y_1742_ = v_a_1736_;
v___y_1743_ = v_a_1737_;
goto v___jp_1739_;
}
}
v___jp_1739_:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_Elab_Info_toElabInfo_x3f(v_i_1733_);
if (lean_obj_tag(v___x_1744_) == 1)
{
lean_object* v_val_1745_; lean_object* v_elaborator_1746_; lean_object* v_stx_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; lean_object* v___x_1750_; 
v_val_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_val_1745_);
lean_dec_ref_known(v___x_1744_, 1);
v_elaborator_1746_ = lean_ctor_get(v_val_1745_, 0);
lean_inc(v_elaborator_1746_);
v_stx_1747_ = lean_ctor_get(v_val_1745_, 1);
lean_inc(v_stx_1747_);
lean_dec(v_val_1745_);
v___x_1748_ = l_Lean_Syntax_getKind(v_stx_1747_);
v___x_1749_ = 1;
v___x_1750_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v___x_1748_, v___x_1749_, v___y_1742_, v___y_1743_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
if (lean_obj_tag(v_a_1751_) == 0)
{
lean_object* v___x_1752_; 
lean_dec_ref_known(v___x_1750_, 1);
v___x_1752_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_elaborator_1746_, v___x_1749_, v___y_1742_, v___y_1743_);
return v___x_1752_;
}
else
{
lean_dec(v_elaborator_1746_);
return v___x_1750_;
}
}
else
{
lean_dec(v_elaborator_1746_);
return v___x_1750_;
}
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec(v___x_1744_);
v___x_1753_ = lean_box(0);
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
return v___x_1754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_docString_x3f___boxed(lean_object* v_i_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_Elab_Info_docString_x3f(v_i_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
return v_res_1899_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1900_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
return v___x_1902_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1903_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1904_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1905_ = lean_unsigned_to_nat(0u);
v___x_1906_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
lean_ctor_set(v___x_1906_, 2, v___x_1905_);
lean_ctor_set(v___x_1906_, 3, v___x_1905_);
lean_ctor_set(v___x_1906_, 4, v___x_1904_);
lean_ctor_set(v___x_1906_, 5, v___x_1904_);
lean_ctor_set(v___x_1906_, 6, v___x_1904_);
lean_ctor_set(v___x_1906_, 7, v___x_1904_);
lean_ctor_set(v___x_1906_, 8, v___x_1904_);
lean_ctor_set(v___x_1906_, 9, v___x_1904_);
lean_ctor_set(v___x_1906_, 10, v___x_1904_);
lean_ctor_set(v___x_1906_, 11, v___x_1903_);
return v___x_1906_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1907_ = lean_unsigned_to_nat(32u);
v___x_1908_ = lean_mk_empty_array_with_capacity(v___x_1907_);
v___x_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
return v___x_1909_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1910_ = ((size_t)5ULL);
v___x_1911_ = lean_unsigned_to_nat(0u);
v___x_1912_ = lean_unsigned_to_nat(32u);
v___x_1913_ = lean_mk_empty_array_with_capacity(v___x_1912_);
v___x_1914_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1915_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
lean_ctor_set(v___x_1915_, 1, v___x_1913_);
lean_ctor_set(v___x_1915_, 2, v___x_1911_);
lean_ctor_set(v___x_1915_, 3, v___x_1911_);
lean_ctor_set_usize(v___x_1915_, 4, v___x_1910_);
return v___x_1915_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1916_ = lean_box(1);
v___x_1917_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_1918_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1919_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v___x_1917_);
lean_ctor_set(v___x_1919_, 2, v___x_1916_);
return v___x_1919_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1922_ = l_Lean_stringToMessageData(v___x_1921_);
return v___x_1922_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1925_ = l_Lean_stringToMessageData(v___x_1924_);
return v___x_1925_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1928_ = l_Lean_stringToMessageData(v___x_1927_);
return v___x_1928_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1931_ = l_Lean_stringToMessageData(v___x_1930_);
return v___x_1931_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_1934_ = l_Lean_stringToMessageData(v___x_1933_);
return v___x_1934_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_1937_ = l_Lean_stringToMessageData(v___x_1936_);
return v___x_1937_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_1940_ = l_Lean_stringToMessageData(v___x_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1941_, lean_object* v_declHint_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v_env_1947_; uint8_t v___x_1948_; 
v___x_1945_ = lean_box(0);
v___x_1946_ = lean_st_ref_get(v___y_1943_);
v_env_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc_ref(v_env_1947_);
lean_dec(v___x_1946_);
v___x_1948_ = l_Lean_Name_isAnonymous(v_declHint_1942_);
if (v___x_1948_ == 0)
{
uint8_t v_isExporting_1949_; 
v_isExporting_1949_ = lean_ctor_get_uint8(v_env_1947_, sizeof(void*)*13);
if (v_isExporting_1949_ == 0)
{
lean_object* v___x_1950_; 
lean_dec_ref(v_env_1947_);
lean_dec(v_declHint_1942_);
v___x_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1950_, 0, v_msg_1941_);
return v___x_1950_;
}
else
{
lean_object* v___x_1951_; uint8_t v___x_1952_; 
lean_inc_ref(v_env_1947_);
v___x_1951_ = l_Lean_Environment_setExporting(v_env_1947_, v___x_1948_);
lean_inc(v_declHint_1942_);
lean_inc_ref(v___x_1951_);
v___x_1952_ = l_Lean_Environment_contains(v___x_1951_, v_declHint_1942_, v_isExporting_1949_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; 
lean_dec_ref(v___x_1951_);
lean_dec_ref(v_env_1947_);
lean_dec(v_declHint_1942_);
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v_msg_1941_);
return v___x_1953_;
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v_c_1959_; lean_object* v___x_1960_; 
v___x_1954_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_1955_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1956_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1951_);
v___x_1957_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1951_);
lean_ctor_set(v___x_1957_, 1, v___x_1954_);
lean_ctor_set(v___x_1957_, 2, v___x_1955_);
lean_ctor_set(v___x_1957_, 3, v___x_1956_);
lean_inc(v_declHint_1942_);
v___x_1958_ = l_Lean_MessageData_ofConstName(v_declHint_1942_, v___x_1948_);
v_c_1959_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1959_, 0, v___x_1957_);
lean_ctor_set(v_c_1959_, 1, v___x_1958_);
v___x_1960_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1951_, v_declHint_1942_);
lean_dec_ref(v___x_1951_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
lean_dec_ref(v_env_1947_);
lean_dec(v_declHint_1942_);
v___x_1961_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
lean_ctor_set(v___x_1962_, 1, v_c_1959_);
v___x_1963_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = l_Lean_MessageData_note(v___x_1964_);
v___x_1966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1966_, 0, v_msg_1941_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
return v___x_1967_;
}
else
{
lean_object* v_val_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_2002_; 
v_val_1968_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1970_ = v___x_1960_;
v_isShared_1971_ = v_isSharedCheck_2002_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_val_1968_);
lean_dec(v___x_1960_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_2002_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; lean_object* v_moduleNames_1973_; lean_object* v_mod_1974_; uint8_t v___x_1975_; 
v___x_1972_ = l_Lean_Environment_header(v_env_1947_);
lean_dec_ref(v_env_1947_);
v_moduleNames_1973_ = lean_ctor_get(v___x_1972_, 4);
lean_inc_ref(v_moduleNames_1973_);
lean_dec_ref(v___x_1972_);
v_mod_1974_ = lean_array_get(v___x_1945_, v_moduleNames_1973_, v_val_1968_);
lean_dec(v_val_1968_);
lean_dec_ref(v_moduleNames_1973_);
v___x_1975_ = l_Lean_isPrivateName(v_declHint_1942_);
lean_dec(v_declHint_1942_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1976_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
lean_ctor_set(v___x_1977_, 1, v_c_1959_);
v___x_1978_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1977_);
lean_ctor_set(v___x_1979_, 1, v___x_1978_);
v___x_1980_ = l_Lean_MessageData_ofName(v_mod_1974_);
v___x_1981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1979_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
v___x_1982_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_1983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1981_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
v___x_1984_ = l_Lean_MessageData_note(v___x_1983_);
v___x_1985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1985_, 0, v_msg_1941_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set_tag(v___x_1970_, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1985_);
v___x_1987_ = v___x_1970_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
else
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1989_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
lean_ctor_set(v___x_1990_, 1, v_c_1959_);
v___x_1991_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_1992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1990_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = l_Lean_MessageData_ofName(v_mod_1974_);
v___x_1994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1992_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_1996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1994_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = l_Lean_MessageData_note(v___x_1996_);
v___x_1998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1998_, 0, v_msg_1941_);
lean_ctor_set(v___x_1998_, 1, v___x_1997_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set_tag(v___x_1970_, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1998_);
v___x_2000_ = v___x_1970_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2003_; 
lean_dec_ref(v_env_1947_);
lean_dec(v_declHint_1942_);
v___x_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2003_, 0, v_msg_1941_);
return v___x_2003_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_2004_, lean_object* v_declHint_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_2004_, v_declHint_2005_, v___y_2006_);
lean_dec(v___y_2006_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_2009_, lean_object* v_declHint_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v___x_2016_; lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2026_; 
v___x_2016_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_2009_, v_declHint_2010_, v___y_2014_);
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2026_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2026_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2024_; 
v___x_2021_ = l_Lean_unknownIdentifierMessageTag;
v___x_2022_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
lean_ctor_set(v___x_2022_, 1, v_a_2017_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2022_);
v___x_2024_ = v___x_2019_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_2027_, lean_object* v_declHint_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2027_, v_declHint_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object* v_msgData_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v___x_2041_; lean_object* v_env_2042_; uint8_t v___x_2043_; lean_object* v_env_2044_; lean_object* v___x_2045_; lean_object* v_toCold_2046_; lean_object* v_mctx_2047_; lean_object* v_lctx_2048_; lean_object* v_options_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2041_ = lean_st_ref_get(v___y_2039_);
v_env_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc_ref(v_env_2042_);
lean_dec(v___x_2041_);
v___x_2043_ = 0;
v_env_2044_ = l_Lean_Environment_setRecordingDeps(v_env_2042_, v___x_2043_);
v___x_2045_ = lean_st_ref_get(v___y_2037_);
v_toCold_2046_ = lean_ctor_get(v___y_2038_, 0);
v_mctx_2047_ = lean_ctor_get(v___x_2045_, 0);
lean_inc_ref(v_mctx_2047_);
lean_dec(v___x_2045_);
v_lctx_2048_ = lean_ctor_get(v___y_2036_, 2);
v_options_2049_ = lean_ctor_get(v_toCold_2046_, 2);
lean_inc_ref(v_options_2049_);
lean_inc_ref(v_lctx_2048_);
v___x_2050_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2050_, 0, v_env_2044_);
lean_ctor_set(v___x_2050_, 1, v_mctx_2047_);
lean_ctor_set(v___x_2050_, 2, v_lctx_2048_);
lean_ctor_set(v___x_2050_, 3, v_options_2049_);
v___x_2051_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
lean_ctor_set(v___x_2051_, 1, v_msgData_2035_);
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v_ref_2066_; lean_object* v___x_2067_; lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2076_; 
v_ref_2066_ = lean_ctor_get(v___y_2063_, 2);
v___x_2067_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2070_ = v___x_2067_;
v_isShared_2071_ = v_isSharedCheck_2076_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2067_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2076_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; lean_object* v___x_2074_; 
lean_inc(v_ref_2066_);
v___x_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2072_, 0, v_ref_2066_);
lean_ctor_set(v___x_2072_, 1, v_a_2068_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set_tag(v___x_2070_, 1);
lean_ctor_set(v___x_2070_, 0, v___x_2072_);
v___x_2074_ = v___x_2070_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_2084_, lean_object* v_msg_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v_toCold_2091_; lean_object* v_currRecDepth_2092_; lean_object* v_ref_2093_; uint16_t v_optionFlags_2094_; uint8_t v_suppressElabErrors_2095_; uint8_t v_checkDeprecated_2096_; uint8_t v_isRecordingDeps_2097_; lean_object* v_ref_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v_toCold_2091_ = lean_ctor_get(v___y_2088_, 0);
v_currRecDepth_2092_ = lean_ctor_get(v___y_2088_, 1);
v_ref_2093_ = lean_ctor_get(v___y_2088_, 2);
v_optionFlags_2094_ = lean_ctor_get_uint16(v___y_2088_, sizeof(void*)*3);
v_suppressElabErrors_2095_ = lean_ctor_get_uint8(v___y_2088_, sizeof(void*)*3 + 2);
v_checkDeprecated_2096_ = lean_ctor_get_uint8(v___y_2088_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2097_ = lean_ctor_get_uint8(v___y_2088_, sizeof(void*)*3 + 4);
v_ref_2098_ = l_Lean_replaceRef(v_ref_2084_, v_ref_2093_);
lean_inc(v_currRecDepth_2092_);
lean_inc_ref(v_toCold_2091_);
v___x_2099_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2099_, 0, v_toCold_2091_);
lean_ctor_set(v___x_2099_, 1, v_currRecDepth_2092_);
lean_ctor_set(v___x_2099_, 2, v_ref_2098_);
lean_ctor_set_uint16(v___x_2099_, sizeof(void*)*3, v_optionFlags_2094_);
lean_ctor_set_uint8(v___x_2099_, sizeof(void*)*3 + 2, v_suppressElabErrors_2095_);
lean_ctor_set_uint8(v___x_2099_, sizeof(void*)*3 + 3, v_checkDeprecated_2096_);
lean_ctor_set_uint8(v___x_2099_, sizeof(void*)*3 + 4, v_isRecordingDeps_2097_);
v___x_2100_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_2085_, v___y_2086_, v___y_2087_, v___x_2099_, v___y_2089_);
lean_dec_ref_known(v___x_2099_, 3);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_2101_, lean_object* v_msg_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_2101_, v_msg_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v_ref_2101_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_2109_, lean_object* v_msg_2110_, lean_object* v_declHint_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v___x_2117_; lean_object* v_a_2118_; lean_object* v___x_2119_; 
v___x_2117_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2110_, v_declHint_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2118_);
lean_dec_ref(v___x_2117_);
v___x_2119_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_2109_, v_a_2118_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_2120_, lean_object* v_msg_2121_, lean_object* v_declHint_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_2120_, v_msg_2121_, v_declHint_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v_ref_2120_);
return v_res_2128_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_2131_ = l_Lean_stringToMessageData(v___x_2130_);
return v___x_2131_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2));
v___x_2134_ = l_Lean_stringToMessageData(v___x_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_2135_, lean_object* v_constName_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v___x_2142_; uint8_t v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2142_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_2143_ = 0;
lean_inc(v_constName_2136_);
v___x_2144_ = l_Lean_MessageData_ofConstName(v_constName_2136_, v___x_2143_);
v___x_2145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2142_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_2147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2145_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_2135_, v___x_2147_, v_constName_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_2149_, lean_object* v_constName_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2149_, v_constName_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v_ref_2149_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v_ref_2163_; lean_object* v___x_2164_; 
v_ref_2163_ = lean_ctor_get(v___y_2160_, 2);
v___x_2164_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2163_, v_constName_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(lean_object* v_constName_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2178_; lean_object* v_env_2179_; uint8_t v___x_2180_; lean_object* v___x_2181_; 
v___x_2178_ = lean_st_ref_get(v___y_2176_);
v_env_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc_ref(v_env_2179_);
lean_dec(v___x_2178_);
v___x_2180_ = 0;
lean_inc(v_constName_2172_);
v___x_2181_ = l_Lean_Environment_find_x3f(v_env_2179_, v_constName_2172_, v___x_2180_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
return v___x_2182_;
}
else
{
lean_object* v_val_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_dec(v_constName_2172_);
v_val_2183_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2181_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_val_2183_);
lean_dec(v___x_2181_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
lean_ctor_set_tag(v___x_2185_, 0);
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_val_2183_);
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
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0___boxed(lean_object* v_constName_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(v_constName_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(lean_object* v_declName_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = lean_box(0);
lean_inc(v_declName_2198_);
v___x_2205_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(v_declName_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2231_; 
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2231_ == 0)
{
lean_object* v_unused_2232_; 
v_unused_2232_ = lean_ctor_get(v___x_2205_, 0);
lean_dec(v_unused_2232_);
v___x_2207_ = v___x_2205_;
v_isShared_2208_ = v_isSharedCheck_2231_;
goto v_resetjp_2206_;
}
else
{
lean_dec(v___x_2205_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2231_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2209_; lean_object* v_env_2210_; lean_object* v___x_2211_; 
v___x_2209_ = lean_st_ref_get(v___y_2202_);
v_env_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc_ref(v_env_2210_);
lean_dec(v___x_2209_);
v___x_2211_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2210_, v_declName_2198_);
lean_dec(v_declName_2198_);
lean_dec_ref(v_env_2210_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2212_ = lean_box(0);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2212_);
v___x_2214_ = v___x_2207_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
else
{
lean_object* v_val_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2230_; 
v_val_2216_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2218_ = v___x_2211_;
v_isShared_2219_ = v_isSharedCheck_2230_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_val_2216_);
lean_dec(v___x_2211_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2230_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; lean_object* v_env_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2220_ = lean_st_ref_get(v___y_2202_);
v_env_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc_ref(v_env_2221_);
lean_dec(v___x_2220_);
v___x_2222_ = l_Lean_Environment_allImportedModuleNames(v_env_2221_);
lean_dec_ref(v_env_2221_);
v___x_2223_ = lean_array_get(v___x_2204_, v___x_2222_, v_val_2216_);
lean_dec(v_val_2216_);
lean_dec_ref(v___x_2222_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 0, v___x_2223_);
v___x_2225_ = v___x_2218_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2227_; 
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2225_);
v___x_2227_ = v___x_2207_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec(v_declName_2198_);
v_a_2233_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2205_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2205_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0___boxed(lean_object* v_declName_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(v_declName_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(lean_object* v_decl_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(v_decl_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2287_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2263_ = v___x_2260_;
v_isShared_2264_ = v_isSharedCheck_2287_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2260_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2287_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
if (lean_obj_tag(v_a_2261_) == 1)
{
lean_object* v_val_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2282_; 
v_val_2265_ = lean_ctor_get(v_a_2261_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v_a_2261_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2267_ = v_a_2261_;
v_isShared_2268_ = v_isSharedCheck_2282_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_val_2265_);
lean_dec(v_a_2261_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2282_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2269_; uint8_t v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2269_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__1));
v___x_2270_ = 1;
v___x_2271_ = l_Lean_Name_toString(v_val_2265_, v___x_2270_);
v___x_2272_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
v___x_2273_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2269_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
v___x_2274_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__3));
v___x_2275_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2273_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 0, v___x_2275_);
v___x_2277_ = v___x_2267_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
lean_object* v___x_2279_; 
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 0, v___x_2277_);
v___x_2279_ = v___x_2263_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2277_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
else
{
lean_object* v___x_2283_; lean_object* v___x_2285_; 
lean_dec(v_a_2261_);
v___x_2283_ = lean_box(0);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 0, v___x_2283_);
v___x_2285_ = v___x_2263_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2283_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
v_a_2288_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2260_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2260_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___boxed(lean_object* v_decl_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(v_decl_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2303_, lean_object* v_constName_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2311_, lean_object* v_constName_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1(v_00_u03b1_2311_, v_constName_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2319_, lean_object* v_ref_2320_, lean_object* v_constName_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v___x_2327_; 
v___x_2327_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2320_, v_constName_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2328_, lean_object* v_ref_2329_, lean_object* v_constName_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2328_, v_ref_2329_, v_constName_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v_ref_2329_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_2337_, lean_object* v_ref_2338_, lean_object* v_msg_2339_, lean_object* v_declHint_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_2338_, v_msg_2339_, v_declHint_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2347_, lean_object* v_ref_2348_, lean_object* v_msg_2349_, lean_object* v_declHint_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_00_u03b1_2347_, v_ref_2348_, v_msg_2349_, v_declHint_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v_ref_2348_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_2357_, lean_object* v_declHint_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_2357_, v_declHint_2358_, v___y_2362_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2365_, lean_object* v_declHint_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_2365_, v_declHint_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_2373_, lean_object* v_ref_2374_, lean_object* v_msg_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_2374_, v_msg_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2382_, lean_object* v_ref_2383_, lean_object* v_msg_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_2382_, v_ref_2383_, v_msg_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v_ref_2383_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_2391_, lean_object* v_msg_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2399_, lean_object* v_msg_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_2399_, v_msg_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
return v_res_2406_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(lean_object* v_a_2407_){
_start:
{
switch(lean_obj_tag(v_a_2407_))
{
case 3:
{
uint8_t v___x_2408_; 
v___x_2408_ = 1;
return v___x_2408_;
}
case 6:
{
lean_object* v_a_2409_; 
v_a_2409_ = lean_ctor_get(v_a_2407_, 0);
v_a_2407_ = v_a_2409_;
goto _start;
}
case 4:
{
lean_object* v_f_2411_; 
v_f_2411_ = lean_ctor_get(v_a_2407_, 1);
v_a_2407_ = v_f_2411_;
goto _start;
}
case 7:
{
lean_object* v_a_2413_; 
v_a_2413_ = lean_ctor_get(v_a_2407_, 1);
v_a_2407_ = v_a_2413_;
goto _start;
}
default: 
{
uint8_t v___x_2415_; 
v___x_2415_ = 0;
return v___x_2415_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat___boxed(lean_object* v_a_2416_){
_start:
{
uint8_t v_res_2417_; lean_object* v_r_2418_; 
v_res_2417_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(v_a_2416_);
lean_dec(v_a_2416_);
v_r_2418_ = lean_box(v_res_2417_);
return v_r_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(lean_object* v_e_2419_, lean_object* v___y_2420_){
_start:
{
uint8_t v___x_2422_; 
v___x_2422_ = l_Lean_Expr_hasMVar(v_e_2419_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; 
v___x_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2423_, 0, v_e_2419_);
return v___x_2423_;
}
else
{
lean_object* v___x_2424_; lean_object* v_mctx_2425_; lean_object* v___x_2426_; lean_object* v_fst_2427_; lean_object* v_snd_2428_; lean_object* v___x_2429_; lean_object* v_cache_2430_; lean_object* v_zetaDeltaFVarIds_2431_; lean_object* v_postponed_2432_; lean_object* v_diag_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2442_; 
v___x_2424_ = lean_st_ref_get(v___y_2420_);
v_mctx_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc_ref(v_mctx_2425_);
lean_dec(v___x_2424_);
v___x_2426_ = l_Lean_instantiateMVarsCore(v_mctx_2425_, v_e_2419_);
v_fst_2427_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_fst_2427_);
v_snd_2428_ = lean_ctor_get(v___x_2426_, 1);
lean_inc(v_snd_2428_);
lean_dec_ref(v___x_2426_);
v___x_2429_ = lean_st_ref_take(v___y_2420_);
v_cache_2430_ = lean_ctor_get(v___x_2429_, 1);
v_zetaDeltaFVarIds_2431_ = lean_ctor_get(v___x_2429_, 2);
v_postponed_2432_ = lean_ctor_get(v___x_2429_, 3);
v_diag_2433_ = lean_ctor_get(v___x_2429_, 4);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2442_ == 0)
{
lean_object* v_unused_2443_; 
v_unused_2443_ = lean_ctor_get(v___x_2429_, 0);
lean_dec(v_unused_2443_);
v___x_2435_ = v___x_2429_;
v_isShared_2436_ = v_isSharedCheck_2442_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_diag_2433_);
lean_inc(v_postponed_2432_);
lean_inc(v_zetaDeltaFVarIds_2431_);
lean_inc(v_cache_2430_);
lean_dec(v___x_2429_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2442_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v_snd_2428_);
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_snd_2428_);
lean_ctor_set(v_reuseFailAlloc_2441_, 1, v_cache_2430_);
lean_ctor_set(v_reuseFailAlloc_2441_, 2, v_zetaDeltaFVarIds_2431_);
lean_ctor_set(v_reuseFailAlloc_2441_, 3, v_postponed_2432_);
lean_ctor_set(v_reuseFailAlloc_2441_, 4, v_diag_2433_);
v___x_2438_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = lean_st_ref_put(v___y_2420_, v___x_2438_);
v___x_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2440_, 0, v_fst_2427_);
return v___x_2440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg___boxed(lean_object* v_e_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_e_2444_, v___y_2445_);
lean_dec(v___y_2445_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0(lean_object* v_e_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_e_2448_, v___y_2450_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___boxed(lean_object* v_e_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0(v_e_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(lean_object* v_i_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
switch(lean_obj_tag(v_i_2473_))
{
case 1:
{
lean_object* v_i_2479_; lean_object* v_expr_2480_; uint8_t v_isDisplayableTerm_2481_; lean_object* v___x_2482_; lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2603_; 
v_i_2479_ = lean_ctor_get(v_i_2473_, 0);
lean_inc_ref(v_i_2479_);
lean_dec_ref_known(v_i_2473_, 1);
v_expr_2480_ = lean_ctor_get(v_i_2479_, 3);
lean_inc_ref(v_expr_2480_);
v_isDisplayableTerm_2481_ = lean_ctor_get_uint8(v_i_2479_, sizeof(void*)*4 + 1);
lean_dec_ref(v_i_2479_);
v___x_2482_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_expr_2480_, v_a_2475_);
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2485_ = v___x_2482_;
v_isShared_2486_ = v_isSharedCheck_2603_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2482_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2603_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
uint8_t v___x_2487_; 
v___x_2487_ = l_Lean_Expr_isSort(v_a_2483_);
if (v___x_2487_ == 0)
{
lean_object* v___x_2488_; 
lean_del_object(v___x_2485_);
lean_inc(v_a_2477_);
lean_inc_ref(v_a_2476_);
lean_inc(v_a_2475_);
lean_inc_ref(v_a_2474_);
lean_inc(v_a_2483_);
v___x_2488_ = lean_infer_type(v_a_2483_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_a_2489_; lean_object* v___x_2490_; lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2590_; 
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_a_2489_);
lean_dec_ref_known(v___x_2488_, 1);
v___x_2490_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_a_2489_, v_a_2475_);
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2493_ = v___x_2490_;
v_isShared_2494_ = v_isSharedCheck_2590_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2490_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2590_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Lean_Meta_ppExpr(v_a_2491_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
if (lean_obj_tag(v___x_2495_) == 0)
{
if (lean_obj_tag(v_a_2483_) == 4)
{
lean_object* v_declName_2496_; lean_object* v___x_2497_; 
lean_dec_ref_known(v___x_2495_, 1);
v_declName_2496_ = lean_ctor_get(v_a_2483_, 0);
lean_inc_n(v_declName_2496_, 2);
lean_dec_ref_known(v_a_2483_, 2);
v___x_2497_ = l_Lean_PrettyPrinter_ppSignature(v_declName_2496_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2499_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___x_2497_, 1);
v___x_2499_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(v_declName_2496_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2524_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2502_ = v___x_2499_;
v_isShared_2503_ = v_isSharedCheck_2524_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2499_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2524_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v_fmt_2504_; lean_object* v_infos_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2523_; 
v_fmt_2504_ = lean_ctor_get(v_a_2498_, 0);
v_infos_2505_ = lean_ctor_get(v_a_2498_, 1);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_a_2498_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2507_ = v_a_2498_;
v_isShared_2508_ = v_isSharedCheck_2523_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_infos_2505_);
lean_inc(v_fmt_2504_);
lean_dec(v_a_2498_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2523_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2514_; 
v___x_2509_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1));
v___x_2510_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
lean_ctor_set(v___x_2510_, 1, v_fmt_2504_);
v___x_2511_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3));
v___x_2512_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2510_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 0, v___x_2512_);
v___x_2514_ = v___x_2507_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_infos_2505_);
v___x_2514_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2516_; 
if (v_isShared_2494_ == 0)
{
lean_ctor_set_tag(v___x_2493_, 1);
lean_ctor_set(v___x_2493_, 0, v___x_2514_);
v___x_2516_ = v___x_2493_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2516_);
lean_ctor_set(v___x_2517_, 1, v_a_2500_);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 0, v___x_2517_);
v___x_2519_ = v___x_2502_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2517_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
lean_dec(v_a_2498_);
lean_del_object(v___x_2493_);
v_a_2525_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2499_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2499_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec(v_declName_2496_);
lean_del_object(v___x_2493_);
v_a_2533_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2497_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2497_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2542_; 
v_a_2541_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2541_);
lean_dec_ref_known(v___x_2495_, 1);
lean_inc(v_a_2483_);
v___x_2542_ = l_Lean_Meta_ppExpr(v_a_2483_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2573_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2545_ = v___x_2542_;
v_isShared_2546_ = v_isSharedCheck_2573_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2542_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2573_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___y_2548_; 
if (v_isDisplayableTerm_2481_ == 0)
{
if (lean_obj_tag(v_a_2483_) == 1)
{
lean_object* v_lctx_2567_; lean_object* v___x_2568_; 
v_lctx_2567_ = lean_ctor_get(v_a_2474_, 2);
lean_inc_ref(v_lctx_2567_);
v___x_2568_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_2567_, v_a_2483_);
lean_dec_ref_known(v_a_2483_, 1);
if (lean_obj_tag(v___x_2568_) == 1)
{
lean_object* v_val_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v_val_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_val_2569_);
lean_dec_ref_known(v___x_2568_, 1);
v___x_2570_ = l_Lean_LocalDecl_userName(v_val_2569_);
lean_dec(v_val_2569_);
v___x_2571_ = l_Lean_Name_hasMacroScopes(v___x_2570_);
lean_dec(v___x_2570_);
if (v___x_2571_ == 0)
{
goto v___jp_2563_;
}
else
{
lean_dec(v_a_2543_);
v___y_2548_ = v_a_2541_;
goto v___jp_2547_;
}
}
else
{
lean_dec(v___x_2568_);
lean_dec(v_a_2543_);
v___y_2548_ = v_a_2541_;
goto v___jp_2547_;
}
}
else
{
uint8_t v___x_2572_; 
lean_dec(v_a_2483_);
v___x_2572_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(v_a_2543_);
if (v___x_2572_ == 0)
{
lean_dec(v_a_2543_);
v___y_2548_ = v_a_2541_;
goto v___jp_2547_;
}
else
{
goto v___jp_2563_;
}
}
}
else
{
lean_dec(v_a_2483_);
goto v___jp_2563_;
}
v___jp_2547_:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2556_; 
v___x_2549_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1));
v___x_2550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
lean_ctor_set(v___x_2550_, 1, v___y_2548_);
v___x_2551_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3));
v___x_2552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2550_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = lean_box(1);
v___x_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2552_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set_tag(v___x_2493_, 1);
lean_ctor_set(v___x_2493_, 0, v___x_2554_);
v___x_2556_ = v___x_2493_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2554_);
v___x_2556_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2560_; 
v___x_2557_ = lean_box(0);
v___x_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2556_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___x_2558_);
v___x_2560_ = v___x_2545_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
v___jp_2563_:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2564_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5));
v___x_2565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2565_, 0, v_a_2543_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
v___x_2566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
lean_ctor_set(v___x_2566_, 1, v_a_2541_);
v___y_2548_ = v___x_2566_;
goto v___jp_2547_;
}
}
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec(v_a_2541_);
lean_del_object(v___x_2493_);
lean_dec(v_a_2483_);
v_a_2574_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2542_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2542_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
lean_del_object(v___x_2493_);
lean_dec(v_a_2483_);
v_a_2582_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2495_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2495_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec(v_a_2483_);
v_a_2591_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2488_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2488_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
else
{
lean_object* v___x_2599_; lean_object* v___x_2601_; 
lean_dec(v_a_2483_);
v___x_2599_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6));
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___x_2599_);
v___x_2601_ = v___x_2485_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2599_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
case 7:
{
lean_object* v_i_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2654_; 
v_i_2604_ = lean_ctor_get(v_i_2473_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v_i_2473_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2606_ = v_i_2473_;
v_isShared_2607_ = v_isSharedCheck_2654_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_i_2604_);
lean_dec(v_i_2473_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2654_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v_fieldName_2608_; lean_object* v_val_2609_; lean_object* v___x_2610_; 
v_fieldName_2608_ = lean_ctor_get(v_i_2604_, 1);
lean_inc(v_fieldName_2608_);
v_val_2609_ = lean_ctor_get(v_i_2604_, 3);
lean_inc_ref(v_val_2609_);
lean_dec_ref(v_i_2604_);
lean_inc(v_a_2477_);
lean_inc_ref(v_a_2476_);
lean_inc(v_a_2475_);
lean_inc_ref(v_a_2474_);
v___x_2610_ = lean_infer_type(v_val_2609_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2612_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref_known(v___x_2610_, 1);
v___x_2612_ = l_Lean_Meta_ppExpr(v_a_2611_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2637_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2615_ = v___x_2612_;
v_isShared_2616_ = v_isSharedCheck_2637_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2612_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2637_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2617_; uint8_t v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2621_; 
v___x_2617_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1));
v___x_2618_ = 1;
v___x_2619_ = l_Lean_Name_toString(v_fieldName_2608_, v___x_2618_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set_tag(v___x_2606_, 3);
lean_ctor_set(v___x_2606_, 0, v___x_2619_);
v___x_2621_ = v___x_2606_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2617_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
v___x_2623_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5));
v___x_2624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2622_);
lean_ctor_set(v___x_2624_, 1, v___x_2623_);
v___x_2625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2624_);
lean_ctor_set(v___x_2625_, 1, v_a_2613_);
v___x_2626_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3));
v___x_2627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2625_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = lean_box(1);
v___x_2629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2627_);
lean_ctor_set(v___x_2629_, 1, v___x_2628_);
v___x_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2629_);
v___x_2631_ = lean_box(0);
v___x_2632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2630_);
lean_ctor_set(v___x_2632_, 1, v___x_2631_);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v___x_2632_);
v___x_2634_ = v___x_2615_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2632_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec(v_fieldName_2608_);
lean_del_object(v___x_2606_);
v_a_2638_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2612_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2612_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec(v_fieldName_2608_);
lean_del_object(v___x_2606_);
v_a_2646_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2610_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2610_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
}
default: 
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
lean_dec_ref(v_i_2473_);
v___x_2655_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6));
v___x_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
return v___x_2656_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___boxed(lean_object* v_i_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(v_i_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__0(lean_object* v_snd_2664_, lean_object* v_____r_2665_, lean_object* v_fmts_2666_, lean_object* v_infos_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2673_, 0, v_fmts_2666_);
lean_ctor_set(v___x_2673_, 1, v_infos_2667_);
v___x_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2674_, 0, v_snd_2664_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2674_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__0___boxed(lean_object* v_snd_2676_, lean_object* v_____r_2677_, lean_object* v_fmts_2678_, lean_object* v_infos_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(v_snd_2676_, v_____r_2677_, v_fmts_2678_, v_infos_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0_spec__0(lean_object* v_x_2686_, lean_object* v_x_2687_, lean_object* v_x_2688_){
_start:
{
if (lean_obj_tag(v_x_2688_) == 0)
{
lean_dec(v_x_2686_);
return v_x_2687_;
}
else
{
lean_object* v_head_2689_; lean_object* v_tail_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2699_; 
v_head_2689_ = lean_ctor_get(v_x_2688_, 0);
v_tail_2690_ = lean_ctor_get(v_x_2688_, 1);
v_isSharedCheck_2699_ = !lean_is_exclusive(v_x_2688_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2692_ = v_x_2688_;
v_isShared_2693_ = v_isSharedCheck_2699_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_tail_2690_);
lean_inc(v_head_2689_);
lean_dec(v_x_2688_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2699_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
lean_inc(v_x_2686_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set_tag(v___x_2692_, 5);
lean_ctor_set(v___x_2692_, 1, v_x_2686_);
lean_ctor_set(v___x_2692_, 0, v_x_2687_);
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_x_2687_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_x_2686_);
v___x_2695_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
lean_object* v___x_2696_; 
v___x_2696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
lean_ctor_set(v___x_2696_, 1, v_head_2689_);
v_x_2687_ = v___x_2696_;
v_x_2688_ = v_tail_2690_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0(lean_object* v_x_2700_, lean_object* v_x_2701_){
_start:
{
if (lean_obj_tag(v_x_2700_) == 0)
{
lean_object* v___x_2702_; 
lean_dec(v_x_2701_);
v___x_2702_ = lean_box(0);
return v___x_2702_;
}
else
{
lean_object* v_tail_2703_; 
v_tail_2703_ = lean_ctor_get(v_x_2700_, 1);
if (lean_obj_tag(v_tail_2703_) == 0)
{
lean_object* v_head_2704_; 
lean_dec(v_x_2701_);
v_head_2704_ = lean_ctor_get(v_x_2700_, 0);
lean_inc(v_head_2704_);
lean_dec_ref_known(v_x_2700_, 2);
return v_head_2704_;
}
else
{
lean_object* v_head_2705_; lean_object* v___x_2706_; 
lean_inc(v_tail_2703_);
v_head_2705_ = lean_ctor_get(v_x_2700_, 0);
lean_inc(v_head_2705_);
lean_dec_ref_known(v_x_2700_, 2);
v___x_2706_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0_spec__0(v_x_2701_, v_head_2705_, v_tail_2703_);
return v___x_2706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__1(lean_object* v___x_2710_, lean_object* v_i_2711_, lean_object* v_fmts_2712_, lean_object* v_infos_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
lean_object* v___y_2720_; lean_object* v_fmts_2721_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v_fmts_2735_; lean_object* v_fst_2739_; lean_object* v_fst_2740_; lean_object* v_snd_2741_; lean_object* v_a_2762_; lean_object* v___y_2769_; lean_object* v___x_2775_; 
lean_inc_ref(v_i_2711_);
v___x_2775_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(v_i_2711_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
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
lean_dec(v_infos_2713_);
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
v___x_2782_ = lean_array_push(v_fmts_2712_, v_fmt_2780_);
v___x_2783_ = lean_box(0);
v___x_2784_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(v_snd_2779_, v___x_2783_, v___x_2782_, v_infos_2781_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
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
v___x_2787_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(v_snd_2785_, v___x_2786_, v_fmts_2712_, v_infos_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
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
v_a_2762_ = v_a_2788_;
goto v___jp_2761_;
}
v___jp_2719_:
{
lean_object* v___x_2722_; uint8_t v___x_2723_; 
v___x_2722_ = lean_array_get_size(v_fmts_2721_);
v___x_2723_ = lean_nat_dec_eq(v___x_2722_, v___x_2710_);
if (v___x_2723_ == 0)
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2724_ = lean_array_to_list(v_fmts_2721_);
v___x_2725_ = ((lean_object*)(l_Lean_Elab_Info_fmtHover_x3f___lam__1___closed__1));
v___x_2726_ = l_Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0(v___x_2724_, v___x_2725_);
v___x_2727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
lean_ctor_set(v___x_2727_, 1, v___y_2720_);
v___x_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2727_);
v___x_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
return v___x_2729_;
}
else
{
lean_object* v___x_2730_; lean_object* v___x_2731_; 
lean_dec_ref(v_fmts_2721_);
lean_dec(v___y_2720_);
v___x_2730_ = lean_box(0);
v___x_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2730_);
return v___x_2731_;
}
}
v___jp_2732_:
{
if (lean_obj_tag(v___y_2733_) == 1)
{
lean_object* v_val_2736_; lean_object* v___x_2737_; 
v_val_2736_ = lean_ctor_get(v___y_2733_, 0);
lean_inc(v_val_2736_);
lean_dec_ref_known(v___y_2733_, 1);
v___x_2737_ = lean_array_push(v_fmts_2735_, v_val_2736_);
v___y_2720_ = v___y_2734_;
v_fmts_2721_ = v___x_2737_;
goto v___jp_2719_;
}
else
{
lean_dec(v___y_2733_);
v___y_2720_ = v___y_2734_;
v_fmts_2721_ = v_fmts_2735_;
goto v___jp_2719_;
}
}
v___jp_2738_:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_Lean_Elab_Info_docString_x3f(v_i_2711_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref_known(v___x_2742_, 1);
if (lean_obj_tag(v_a_2743_) == 1)
{
lean_object* v_val_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2752_; 
v_val_2744_ = lean_ctor_get(v_a_2743_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v_a_2743_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2746_ = v_a_2743_;
v_isShared_2747_ = v_isSharedCheck_2752_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_val_2744_);
lean_dec(v_a_2743_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2752_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
lean_ctor_set_tag(v___x_2746_, 3);
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_val_2744_);
v___x_2749_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_object* v___x_2750_; 
v___x_2750_ = lean_array_push(v_fst_2740_, v___x_2749_);
v___y_2733_ = v_fst_2739_;
v___y_2734_ = v_snd_2741_;
v_fmts_2735_ = v___x_2750_;
goto v___jp_2732_;
}
}
}
else
{
lean_dec(v_a_2743_);
v___y_2733_ = v_fst_2739_;
v___y_2734_ = v_snd_2741_;
v_fmts_2735_ = v_fst_2740_;
goto v___jp_2732_;
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
lean_dec(v_snd_2741_);
lean_dec(v_fst_2740_);
lean_dec(v_fst_2739_);
v_a_2753_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2742_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2742_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
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
v___jp_2761_:
{
uint8_t v___x_2763_; 
v___x_2763_ = l_Lean_Exception_isInterrupt(v_a_2762_);
if (v___x_2763_ == 0)
{
uint8_t v___x_2764_; 
lean_inc_ref(v_a_2762_);
v___x_2764_ = l_Lean_Exception_isRuntime(v_a_2762_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; 
lean_dec_ref(v_a_2762_);
v___x_2765_ = lean_box(0);
v_fst_2739_ = v___x_2765_;
v_fst_2740_ = v_fmts_2712_;
v_snd_2741_ = v_infos_2713_;
goto v___jp_2738_;
}
else
{
lean_object* v___x_2766_; 
lean_dec(v_infos_2713_);
lean_dec_ref(v_fmts_2712_);
lean_dec_ref(v_i_2711_);
v___x_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2766_, 0, v_a_2762_);
return v___x_2766_;
}
}
else
{
lean_object* v___x_2767_; 
lean_dec(v_infos_2713_);
lean_dec_ref(v_fmts_2712_);
lean_dec_ref(v_i_2711_);
v___x_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2767_, 0, v_a_2762_);
return v___x_2767_;
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
v_fst_2739_ = v_fst_2772_;
v_fst_2740_ = v_fst_2773_;
v_snd_2741_ = v_snd_2774_;
goto v___jp_2738_;
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
size_t v___x_2843_; size_t v___x_2844_; uint8_t v___x_2845_; 
v___x_2843_ = ((size_t)0ULL);
v___x_2844_ = lean_usize_of_nat(v___x_2841_);
v___x_2845_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(v_hoverPos_2835_, v_pos_2836_, v_tailPos_2837_, v_cs_2839_, v___x_2843_, v___x_2844_);
return v___x_2845_;
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
size_t v___x_2850_; size_t v___x_2851_; uint8_t v___x_2852_; 
v___x_2850_ = ((size_t)0ULL);
v___x_2851_ = lean_usize_of_nat(v___x_2848_);
v___x_2852_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_2835_, v_pos_2836_, v_tailPos_2837_, v_vs_2846_, v___x_2850_, v___x_2851_);
return v___x_2852_;
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
size_t v___x_2863_; size_t v___x_2864_; uint8_t v___x_2865_; 
v___x_2863_ = ((size_t)0ULL);
v___x_2864_ = lean_usize_of_nat(v___x_2861_);
v___x_2865_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_2853_, v_pos_2854_, v_tailPos_2855_, v_tail_2858_, v___x_2863_, v___x_2864_);
return v___x_2865_;
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
lean_object* v_val_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; uint8_t v___x_2881_; 
v_val_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_val_2878_);
lean_dec_ref_known(v___x_2877_, 1);
v___x_2879_ = lean_unsigned_to_nat(1u);
v___x_2880_ = lean_nat_add(v_hoverPos_2866_, v___x_2879_);
v___x_2881_ = lean_nat_dec_le(v___x_2880_, v_val_2878_);
lean_dec(v___x_2880_);
if (v___x_2881_ == 0)
{
uint8_t v___x_2882_; 
lean_dec(v_val_2878_);
lean_dec(v_val_2876_);
v___x_2882_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2866_, v_pos_2867_, v_tailPos_2868_, v_children_2871_);
return v___x_2882_;
}
else
{
uint8_t v_decide_2883_; 
v_decide_2883_ = lean_nat_dec_eq(v_val_2876_, v_pos_2867_);
lean_dec(v_val_2876_);
if (v_decide_2883_ == 0)
{
lean_dec(v_val_2878_);
return v___x_2881_;
}
else
{
uint8_t v_decide_2884_; 
v_decide_2884_ = lean_nat_dec_eq(v_val_2878_, v_tailPos_2868_);
lean_dec(v_val_2878_);
if (v_decide_2884_ == 0)
{
return v___x_2881_;
}
else
{
uint8_t v___x_2885_; 
v___x_2885_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2866_, v_pos_2867_, v_tailPos_2868_, v_children_2871_);
return v___x_2885_;
}
}
}
}
else
{
uint8_t v___x_2886_; 
lean_dec(v___x_2877_);
lean_dec(v_val_2876_);
v___x_2886_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2866_, v_pos_2867_, v_tailPos_2868_, v_children_2871_);
return v___x_2886_;
}
}
else
{
uint8_t v___x_2887_; 
lean_dec(v___x_2875_);
v___x_2887_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2866_, v_pos_2867_, v_tailPos_2868_, v_children_2871_);
return v___x_2887_;
}
}
else
{
uint8_t v___x_2888_; 
v___x_2888_ = 0;
return v___x_2888_;
}
}
case 4:
{
lean_object* v_children_2889_; uint8_t v___x_2890_; 
v_children_2889_ = lean_ctor_get(v_a_2869_, 1);
v___x_2890_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2866_, v_pos_2867_, v_tailPos_2868_, v_children_2889_);
return v___x_2890_;
}
default: 
{
uint8_t v___x_2891_; 
v___x_2891_ = 0;
return v___x_2891_;
}
}
}
else
{
uint8_t v___x_2892_; 
v___x_2892_ = 0;
return v___x_2892_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(lean_object* v_hoverPos_2893_, lean_object* v_pos_2894_, lean_object* v_tailPos_2895_, lean_object* v_as_2896_, size_t v_i_2897_, size_t v_stop_2898_){
_start:
{
uint8_t v___x_2899_; 
v___x_2899_ = lean_usize_dec_eq(v_i_2897_, v_stop_2898_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; uint8_t v___x_2901_; 
v___x_2900_ = lean_array_uget_borrowed(v_as_2896_, v_i_2897_);
v___x_2901_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(v_hoverPos_2893_, v_pos_2894_, v_tailPos_2895_, v___x_2900_);
if (v___x_2901_ == 0)
{
size_t v___x_2902_; size_t v___x_2903_; 
v___x_2902_ = ((size_t)1ULL);
v___x_2903_ = lean_usize_add(v_i_2897_, v___x_2902_);
v_i_2897_ = v___x_2903_;
goto _start;
}
else
{
return v___x_2901_;
}
}
else
{
uint8_t v___x_2905_; 
v___x_2905_ = 0;
return v___x_2905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1___boxed(lean_object* v_hoverPos_2906_, lean_object* v_pos_2907_, lean_object* v_tailPos_2908_, lean_object* v_as_2909_, lean_object* v_i_2910_, lean_object* v_stop_2911_){
_start:
{
size_t v_i_boxed_2912_; size_t v_stop_boxed_2913_; uint8_t v_res_2914_; lean_object* v_r_2915_; 
v_i_boxed_2912_ = lean_unbox_usize(v_i_2910_);
lean_dec(v_i_2910_);
v_stop_boxed_2913_ = lean_unbox_usize(v_stop_2911_);
lean_dec(v_stop_2911_);
v_res_2914_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_2906_, v_pos_2907_, v_tailPos_2908_, v_as_2909_, v_i_boxed_2912_, v_stop_boxed_2913_);
lean_dec_ref(v_as_2909_);
lean_dec(v_tailPos_2908_);
lean_dec(v_pos_2907_);
lean_dec(v_hoverPos_2906_);
v_r_2915_ = lean_box(v_res_2914_);
return v_r_2915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1___boxed(lean_object* v_hoverPos_2916_, lean_object* v_pos_2917_, lean_object* v_tailPos_2918_, lean_object* v_as_2919_, lean_object* v_i_2920_, lean_object* v_stop_2921_){
_start:
{
size_t v_i_boxed_2922_; size_t v_stop_boxed_2923_; uint8_t v_res_2924_; lean_object* v_r_2925_; 
v_i_boxed_2922_ = lean_unbox_usize(v_i_2920_);
lean_dec(v_i_2920_);
v_stop_boxed_2923_ = lean_unbox_usize(v_stop_2921_);
lean_dec(v_stop_2921_);
v_res_2924_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(v_hoverPos_2916_, v_pos_2917_, v_tailPos_2918_, v_as_2919_, v_i_boxed_2922_, v_stop_boxed_2923_);
lean_dec_ref(v_as_2919_);
lean_dec(v_tailPos_2918_);
lean_dec(v_pos_2917_);
lean_dec(v_hoverPos_2916_);
v_r_2925_ = lean_box(v_res_2924_);
return v_r_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0___boxed(lean_object* v_hoverPos_2926_, lean_object* v_pos_2927_, lean_object* v_tailPos_2928_, lean_object* v_t_2929_){
_start:
{
uint8_t v_res_2930_; lean_object* v_r_2931_; 
v_res_2930_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2926_, v_pos_2927_, v_tailPos_2928_, v_t_2929_);
lean_dec_ref(v_t_2929_);
lean_dec(v_tailPos_2928_);
lean_dec(v_pos_2927_);
lean_dec(v_hoverPos_2926_);
v_r_2931_ = lean_box(v_res_2930_);
return v_r_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0___boxed(lean_object* v_hoverPos_2932_, lean_object* v_pos_2933_, lean_object* v_tailPos_2934_, lean_object* v_x_2935_){
_start:
{
uint8_t v_res_2936_; lean_object* v_r_2937_; 
v_res_2936_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(v_hoverPos_2932_, v_pos_2933_, v_tailPos_2934_, v_x_2935_);
lean_dec_ref(v_x_2935_);
lean_dec(v_tailPos_2934_);
lean_dec(v_pos_2933_);
lean_dec(v_hoverPos_2932_);
v_r_2937_ = lean_box(v_res_2936_);
return v_r_2937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___boxed(lean_object* v_hoverPos_2938_, lean_object* v_pos_2939_, lean_object* v_tailPos_2940_, lean_object* v_a_2941_){
_start:
{
uint8_t v_res_2942_; lean_object* v_r_2943_; 
v_res_2942_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(v_hoverPos_2938_, v_pos_2939_, v_tailPos_2940_, v_a_2941_);
lean_dec_ref(v_a_2941_);
lean_dec(v_tailPos_2940_);
lean_dec(v_pos_2939_);
lean_dec(v_hoverPos_2938_);
v_r_2943_ = lean_box(v_res_2942_);
return v_r_2943_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock(lean_object* v_stx_2945_){
_start:
{
lean_object* v___x_2946_; uint8_t v___x_2947_; 
v___x_2946_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock___closed__0));
lean_inc(v_stx_2945_);
v___x_2947_ = l_Lean_Syntax_isToken(v___x_2946_, v_stx_2945_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2948_; lean_object* v___x_2949_; uint8_t v___x_2950_; 
v___x_2948_ = l_Lean_Syntax_getNumArgs(v_stx_2945_);
v___x_2949_ = lean_unsigned_to_nat(2u);
v___x_2950_ = lean_nat_dec_eq(v___x_2948_, v___x_2949_);
lean_dec(v___x_2948_);
if (v___x_2950_ == 0)
{
lean_dec(v_stx_2945_);
return v___x_2950_;
}
else
{
lean_object* v___x_2951_; lean_object* v___x_2952_; uint8_t v___x_2953_; 
v___x_2951_ = lean_unsigned_to_nat(0u);
v___x_2952_ = l_Lean_Syntax_getArg(v_stx_2945_, v___x_2951_);
lean_dec(v_stx_2945_);
v___x_2953_ = l_Lean_Syntax_isToken(v___x_2946_, v___x_2952_);
return v___x_2953_;
}
}
else
{
lean_dec(v_stx_2945_);
return v___x_2947_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock___boxed(lean_object* v_stx_2954_){
_start:
{
uint8_t v_res_2955_; lean_object* v_r_2956_; 
v_res_2955_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock(v_stx_2954_);
v_r_2956_ = lean_box(v_res_2955_);
return v_r_2956_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(lean_object* v_x_2957_, lean_object* v_x_2958_){
_start:
{
if (lean_obj_tag(v_x_2957_) == 0)
{
if (lean_obj_tag(v_x_2958_) == 0)
{
uint8_t v___x_2959_; 
v___x_2959_ = 1;
return v___x_2959_;
}
else
{
uint8_t v___x_2960_; 
v___x_2960_ = 0;
return v___x_2960_;
}
}
else
{
if (lean_obj_tag(v_x_2958_) == 0)
{
uint8_t v___x_2961_; 
v___x_2961_ = 0;
return v___x_2961_;
}
else
{
lean_object* v_val_2962_; lean_object* v_val_2963_; uint8_t v___x_2964_; 
v_val_2962_ = lean_ctor_get(v_x_2957_, 0);
v_val_2963_ = lean_ctor_get(v_x_2958_, 0);
v___x_2964_ = lean_nat_dec_eq(v_val_2962_, v_val_2963_);
return v___x_2964_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4___boxed(lean_object* v_x_2965_, lean_object* v_x_2966_){
_start:
{
uint8_t v_res_2967_; lean_object* v_r_2968_; 
v_res_2967_ = l_instBEqOption_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(v_x_2965_, v_x_2966_);
lean_dec(v_x_2966_);
lean_dec(v_x_2965_);
v_r_2968_ = lean_box(v_res_2967_);
return v_r_2968_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(lean_object* v_hoverCol_2969_, lean_object* v_col_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_){
_start:
{
if (lean_obj_tag(v_a_2971_) == 0)
{
lean_object* v___x_2973_; 
v___x_2973_ = l_List_reverse___redArg(v_a_2972_);
return v___x_2973_;
}
else
{
lean_object* v_head_2974_; lean_object* v_tail_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2999_; 
v_head_2974_ = lean_ctor_get(v_a_2971_, 0);
v_tail_2975_ = lean_ctor_get(v_a_2971_, 1);
v_isSharedCheck_2999_ = !lean_is_exclusive(v_a_2971_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2977_ = v_a_2971_;
v_isShared_2978_ = v_isSharedCheck_2999_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_tail_2975_);
lean_inc(v_head_2974_);
lean_dec(v_a_2971_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2999_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___y_2980_; uint8_t v_hangingBy_2985_; 
v_hangingBy_2985_ = lean_ctor_get_uint8(v_head_2974_, sizeof(void*)*3 + 2);
if (v_hangingBy_2985_ == 0)
{
v___y_2980_ = v_head_2974_;
goto v___jp_2979_;
}
else
{
lean_object* v_ctxInfo_2986_; lean_object* v_tacticInfo_2987_; uint8_t v_useAfter_2988_; lean_object* v_priority_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2998_; 
v_ctxInfo_2986_ = lean_ctor_get(v_head_2974_, 0);
v_tacticInfo_2987_ = lean_ctor_get(v_head_2974_, 1);
v_useAfter_2988_ = lean_ctor_get_uint8(v_head_2974_, sizeof(void*)*3);
v_priority_2989_ = lean_ctor_get(v_head_2974_, 2);
v_isSharedCheck_2998_ = !lean_is_exclusive(v_head_2974_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2991_ = v_head_2974_;
v_isShared_2992_ = v_isSharedCheck_2998_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_priority_2989_);
lean_inc(v_tacticInfo_2987_);
lean_inc(v_ctxInfo_2986_);
lean_dec(v_head_2974_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2998_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
uint8_t v___x_2993_; uint8_t v___x_2994_; lean_object* v___x_2996_; 
v___x_2993_ = lean_nat_dec_le(v_hoverCol_2969_, v_col_2970_);
v___x_2994_ = 0;
if (v_isShared_2992_ == 0)
{
v___x_2996_ = v___x_2991_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_ctxInfo_2986_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v_tacticInfo_2987_);
lean_ctor_set(v_reuseFailAlloc_2997_, 2, v_priority_2989_);
lean_ctor_set_uint8(v_reuseFailAlloc_2997_, sizeof(void*)*3, v_useAfter_2988_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
lean_ctor_set_uint8(v___x_2996_, sizeof(void*)*3 + 1, v___x_2993_);
lean_ctor_set_uint8(v___x_2996_, sizeof(void*)*3 + 2, v___x_2994_);
v___y_2980_ = v___x_2996_;
goto v___jp_2979_;
}
}
}
v___jp_2979_:
{
lean_object* v___x_2982_; 
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 1, v_a_2972_);
lean_ctor_set(v___x_2977_, 0, v___y_2980_);
v___x_2982_ = v___x_2977_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___y_2980_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_a_2972_);
v___x_2982_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
v_a_2971_ = v_tail_2975_;
v_a_2972_ = v___x_2982_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0___boxed(lean_object* v_hoverCol_3000_, lean_object* v_col_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(v_hoverCol_3000_, v_col_3001_, v_a_3002_, v_a_3003_);
lean_dec(v_col_3001_);
lean_dec(v_hoverCol_3000_);
return v_res_3004_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(lean_object* v_x_3005_){
_start:
{
if (lean_obj_tag(v_x_3005_) == 0)
{
uint8_t v___x_3006_; 
v___x_3006_ = 1;
return v___x_3006_;
}
else
{
lean_object* v_head_3007_; uint8_t v_indented_3008_; 
v_head_3007_ = lean_ctor_get(v_x_3005_, 0);
v_indented_3008_ = lean_ctor_get_uint8(v_head_3007_, sizeof(void*)*3 + 1);
if (v_indented_3008_ == 0)
{
return v_indented_3008_;
}
else
{
lean_object* v_tail_3009_; 
v_tail_3009_ = lean_ctor_get(v_x_3005_, 1);
v_x_3005_ = v_tail_3009_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1___boxed(lean_object* v_x_3011_){
_start:
{
uint8_t v_res_3012_; lean_object* v_r_3013_; 
v_res_3012_ = l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(v_x_3011_);
lean_dec(v_x_3011_);
v_r_3013_ = lean_box(v_res_3012_);
return v_r_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0(lean_object* v_text_3014_, lean_object* v_column_3015_, lean_object* v_hoverPos_3016_, lean_object* v_ctx_3017_, lean_object* v_i_3018_, lean_object* v_cs_3019_, lean_object* v_gs_3020_){
_start:
{
if (lean_obj_tag(v_i_3018_) == 0)
{
lean_object* v_i_3021_; lean_object* v___x_3022_; 
v_i_3021_ = lean_ctor_get(v_i_3018_, 0);
v___x_3022_ = l_Lean_Elab_Info_pos_x3f(v_i_3018_);
if (lean_obj_tag(v___x_3022_) == 1)
{
lean_object* v_val_3023_; lean_object* v___x_3024_; 
v_val_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_val_3023_);
lean_dec_ref_known(v___x_3022_, 1);
v___x_3024_ = l_Lean_Elab_Info_tailPos_x3f(v_i_3018_);
if (lean_obj_tag(v___x_3024_) == 1)
{
lean_object* v_val_3025_; lean_object* v___x_3026_; lean_object* v_column_3027_; lean_object* v_source_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3074_; 
v_val_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_val_3025_);
lean_dec_ref_known(v___x_3024_, 1);
lean_inc_ref(v_text_3014_);
v___x_3026_ = l_Lean_FileMap_toPosition(v_text_3014_, v_val_3023_);
v_column_3027_ = lean_ctor_get(v___x_3026_, 1);
lean_inc(v_column_3027_);
lean_dec_ref(v___x_3026_);
v_source_3028_ = lean_ctor_get(v_text_3014_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v_text_3014_);
if (v_isSharedCheck_3074_ == 0)
{
lean_object* v_unused_3075_; 
v_unused_3075_ = lean_ctor_get(v_text_3014_, 1);
lean_dec(v_unused_3075_);
v___x_3030_ = v_text_3014_;
v_isShared_3031_ = v_isSharedCheck_3074_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_source_3028_);
lean_dec(v_text_3014_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3074_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3032_; uint8_t v___y_3034_; uint8_t v___y_3035_; uint8_t v___y_3036_; lean_object* v___y_3037_; lean_object* v_gs_3042_; uint8_t v___x_3043_; 
v___x_3032_ = lean_box(0);
v_gs_3042_ = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(v_column_3015_, v_column_3027_, v_gs_3020_, v___x_3032_);
v___x_3043_ = lean_nat_dec_le(v_val_3023_, v_hoverPos_3016_);
if (v___x_3043_ == 0)
{
lean_del_object(v___x_3030_);
lean_dec_ref(v_source_3028_);
lean_dec(v_column_3027_);
lean_dec(v_val_3025_);
lean_dec(v_val_3023_);
lean_dec_ref(v_ctx_3017_);
return v_gs_3042_;
}
else
{
lean_object* v___x_3044_; lean_object* v_trailSize_3045_; lean_object* v___x_3046_; uint8_t v___y_3048_; uint8_t v___y_3055_; uint8_t v___y_3062_; lean_object* v___x_3066_; uint8_t v_atEOF_3067_; lean_object* v___y_3069_; lean_object* v___x_3072_; uint8_t v___x_3073_; 
v___x_3044_ = l_Lean_Elab_Info_stx(v_i_3018_);
v_trailSize_3045_ = l_Lean_Syntax_getTrailingSize(v___x_3044_);
v___x_3046_ = lean_nat_add(v_val_3025_, v_trailSize_3045_);
v___x_3066_ = lean_string_utf8_byte_size(v_source_3028_);
lean_dec_ref(v_source_3028_);
v_atEOF_3067_ = lean_nat_dec_eq(v___x_3046_, v___x_3066_);
v___x_3072_ = lean_unsigned_to_nat(1u);
v___x_3073_ = lean_nat_dec_le(v___x_3072_, v_trailSize_3045_);
if (v___x_3073_ == 0)
{
lean_dec(v_trailSize_3045_);
v___y_3069_ = v___x_3072_;
goto v___jp_3068_;
}
else
{
v___y_3069_ = v_trailSize_3045_;
goto v___jp_3068_;
}
v___jp_3047_:
{
uint8_t v___x_3049_; uint8_t v___x_3050_; uint8_t v___x_3051_; 
v___x_3049_ = lean_nat_dec_lt(v_column_3015_, v_column_3027_);
lean_dec(v_column_3027_);
v___x_3050_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock(v___x_3044_);
v___x_3051_ = lean_nat_dec_eq(v_hoverPos_3016_, v___x_3046_);
lean_dec(v___x_3046_);
if (v___x_3051_ == 0)
{
lean_object* v___x_3052_; 
v___x_3052_ = lean_unsigned_to_nat(1u);
v___y_3034_ = v___x_3050_;
v___y_3035_ = v___y_3048_;
v___y_3036_ = v___x_3049_;
v___y_3037_ = v___x_3052_;
goto v___jp_3033_;
}
else
{
lean_object* v___x_3053_; 
v___x_3053_ = lean_unsigned_to_nat(0u);
v___y_3034_ = v___x_3050_;
v___y_3035_ = v___y_3048_;
v___y_3036_ = v___x_3049_;
v___y_3037_ = v___x_3053_;
goto v___jp_3033_;
}
}
v___jp_3054_:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; uint8_t v___x_3058_; 
v___x_3056_ = lean_unsigned_to_nat(1u);
v___x_3057_ = lean_nat_add(v_val_3023_, v___x_3056_);
v___x_3058_ = lean_nat_dec_le(v___x_3057_, v_hoverPos_3016_);
lean_dec(v___x_3057_);
if (v___x_3058_ == 0)
{
lean_dec(v_val_3025_);
lean_dec(v_val_3023_);
v___y_3048_ = v___x_3058_;
goto v___jp_3047_;
}
else
{
uint8_t v___x_3059_; 
v___x_3059_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_3016_, v_val_3023_, v_val_3025_, v_cs_3019_);
lean_dec(v_val_3025_);
lean_dec(v_val_3023_);
if (v___x_3059_ == 0)
{
v___y_3048_ = v___y_3055_;
goto v___jp_3047_;
}
else
{
uint8_t v___x_3060_; 
v___x_3060_ = 0;
v___y_3048_ = v___x_3060_;
goto v___jp_3047_;
}
}
}
v___jp_3061_:
{
uint8_t v___x_3063_; 
v___x_3063_ = l_List_isEmpty___redArg(v_gs_3042_);
if (v___x_3063_ == 0)
{
uint8_t v___x_3064_; 
v___x_3064_ = lean_nat_dec_le(v_val_3025_, v_hoverPos_3016_);
if (v___x_3064_ == 0)
{
lean_dec(v___x_3046_);
lean_dec(v___x_3044_);
lean_del_object(v___x_3030_);
lean_dec(v_column_3027_);
lean_dec(v_val_3025_);
lean_dec(v_val_3023_);
lean_dec_ref(v_ctx_3017_);
return v_gs_3042_;
}
else
{
uint8_t v___x_3065_; 
v___x_3065_ = l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(v_gs_3042_);
if (v___x_3065_ == 0)
{
lean_dec(v___x_3046_);
lean_dec(v___x_3044_);
lean_del_object(v___x_3030_);
lean_dec(v_column_3027_);
lean_dec(v_val_3025_);
lean_dec(v_val_3023_);
lean_dec_ref(v_ctx_3017_);
return v_gs_3042_;
}
else
{
lean_dec(v_gs_3042_);
v___y_3055_ = v___x_3065_;
goto v___jp_3054_;
}
}
}
else
{
lean_dec(v_gs_3042_);
v___y_3055_ = v___y_3062_;
goto v___jp_3054_;
}
}
v___jp_3068_:
{
lean_object* v___x_3070_; uint8_t v___x_3071_; 
v___x_3070_ = lean_nat_add(v_val_3025_, v___y_3069_);
lean_dec(v___y_3069_);
v___x_3071_ = lean_nat_dec_lt(v_hoverPos_3016_, v___x_3070_);
lean_dec(v___x_3070_);
if (v___x_3071_ == 0)
{
if (v_atEOF_3067_ == 0)
{
lean_dec(v___x_3046_);
lean_dec(v___x_3044_);
lean_del_object(v___x_3030_);
lean_dec(v_column_3027_);
lean_dec(v_val_3025_);
lean_dec(v_val_3023_);
lean_dec_ref(v_ctx_3017_);
return v_gs_3042_;
}
else
{
v___y_3062_ = v_atEOF_3067_;
goto v___jp_3061_;
}
}
else
{
v___y_3062_ = v___x_3071_;
goto v___jp_3061_;
}
}
}
v___jp_3033_:
{
lean_object* v___x_3038_; lean_object* v___x_3040_; 
lean_inc_ref(v_i_3021_);
v___x_3038_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3038_, 0, v_ctx_3017_);
lean_ctor_set(v___x_3038_, 1, v_i_3021_);
lean_ctor_set(v___x_3038_, 2, v___y_3037_);
lean_ctor_set_uint8(v___x_3038_, sizeof(void*)*3, v___y_3035_);
lean_ctor_set_uint8(v___x_3038_, sizeof(void*)*3 + 1, v___y_3036_);
lean_ctor_set_uint8(v___x_3038_, sizeof(void*)*3 + 2, v___y_3034_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set_tag(v___x_3030_, 1);
lean_ctor_set(v___x_3030_, 1, v___x_3032_);
lean_ctor_set(v___x_3030_, 0, v___x_3038_);
v___x_3040_ = v___x_3030_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v___x_3038_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v___x_3032_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
else
{
lean_dec(v___x_3024_);
lean_dec(v_val_3023_);
lean_dec_ref(v_ctx_3017_);
lean_dec_ref(v_text_3014_);
return v_gs_3020_;
}
}
else
{
lean_dec(v___x_3022_);
lean_dec_ref(v_ctx_3017_);
lean_dec_ref(v_text_3014_);
return v_gs_3020_;
}
}
else
{
lean_dec_ref(v_ctx_3017_);
lean_dec_ref(v_text_3014_);
return v_gs_3020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0___boxed(lean_object* v_text_3076_, lean_object* v_column_3077_, lean_object* v_hoverPos_3078_, lean_object* v_ctx_3079_, lean_object* v_i_3080_, lean_object* v_cs_3081_, lean_object* v_gs_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0(v_text_3076_, v_column_3077_, v_hoverPos_3078_, v_ctx_3079_, v_i_3080_, v_cs_3081_, v_gs_3082_);
lean_dec_ref(v_cs_3081_);
lean_dec_ref(v_i_3080_);
lean_dec(v_hoverPos_3078_);
lean_dec(v_column_3077_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3_spec__3(lean_object* v_x_3084_, lean_object* v_x_3085_){
_start:
{
if (lean_obj_tag(v_x_3085_) == 0)
{
lean_inc(v_x_3084_);
return v_x_3084_;
}
else
{
lean_object* v_head_3086_; lean_object* v_tail_3087_; uint8_t v___x_3088_; 
v_head_3086_ = lean_ctor_get(v_x_3085_, 0);
v_tail_3087_ = lean_ctor_get(v_x_3085_, 1);
v___x_3088_ = lean_nat_dec_le(v_x_3084_, v_head_3086_);
if (v___x_3088_ == 0)
{
v_x_3085_ = v_tail_3087_;
goto _start;
}
else
{
v_x_3084_ = v_head_3086_;
v_x_3085_ = v_tail_3087_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3_spec__3___boxed(lean_object* v_x_3091_, lean_object* v_x_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3_spec__3(v_x_3091_, v_x_3092_);
lean_dec(v_x_3092_);
lean_dec(v_x_3091_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(lean_object* v_x_3094_){
_start:
{
if (lean_obj_tag(v_x_3094_) == 0)
{
lean_object* v___x_3095_; 
v___x_3095_ = lean_box(0);
return v___x_3095_;
}
else
{
lean_object* v_head_3096_; lean_object* v_tail_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v_head_3096_ = lean_ctor_get(v_x_3094_, 0);
v_tail_3097_ = lean_ctor_get(v_x_3094_, 1);
v___x_3098_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3_spec__3(v_head_3096_, v_tail_3097_);
v___x_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
return v___x_3099_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3___boxed(lean_object* v_x_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(v_x_3100_);
lean_dec(v_x_3100_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2(lean_object* v_a_3102_, lean_object* v_a_3103_){
_start:
{
if (lean_obj_tag(v_a_3102_) == 0)
{
lean_object* v___x_3104_; 
v___x_3104_ = l_List_reverse___redArg(v_a_3103_);
return v___x_3104_;
}
else
{
lean_object* v_head_3105_; lean_object* v_tail_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3115_; 
v_head_3105_ = lean_ctor_get(v_a_3102_, 0);
v_tail_3106_ = lean_ctor_get(v_a_3102_, 1);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_a_3102_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3108_ = v_a_3102_;
v_isShared_3109_ = v_isSharedCheck_3115_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_tail_3106_);
lean_inc(v_head_3105_);
lean_dec(v_a_3102_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3115_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v_priority_3110_; lean_object* v___x_3112_; 
v_priority_3110_ = lean_ctor_get(v_head_3105_, 2);
lean_inc(v_priority_3110_);
lean_dec(v_head_3105_);
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 1, v_a_3103_);
lean_ctor_set(v___x_3108_, 0, v_priority_3110_);
v___x_3112_ = v___x_3108_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_priority_3110_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v_a_3103_);
v___x_3112_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
v_a_3102_ = v_tail_3106_;
v_a_3103_ = v___x_3112_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__5(lean_object* v_maxPrio_x3f_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_){
_start:
{
if (lean_obj_tag(v_a_3117_) == 0)
{
lean_object* v___x_3119_; 
v___x_3119_ = l_List_reverse___redArg(v_a_3118_);
return v___x_3119_;
}
else
{
lean_object* v_head_3120_; lean_object* v_tail_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3133_; 
v_head_3120_ = lean_ctor_get(v_a_3117_, 0);
v_tail_3121_ = lean_ctor_get(v_a_3117_, 1);
v_isSharedCheck_3133_ = !lean_is_exclusive(v_a_3117_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3123_ = v_a_3117_;
v_isShared_3124_ = v_isSharedCheck_3133_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_tail_3121_);
lean_inc(v_head_3120_);
lean_dec(v_a_3117_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3133_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v_priority_3125_; lean_object* v___x_3126_; uint8_t v___x_3127_; 
v_priority_3125_ = lean_ctor_get(v_head_3120_, 2);
lean_inc(v_priority_3125_);
v___x_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3126_, 0, v_priority_3125_);
v___x_3127_ = l_instBEqOption_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(v___x_3126_, v_maxPrio_x3f_3116_);
lean_dec_ref_known(v___x_3126_, 1);
if (v___x_3127_ == 0)
{
lean_del_object(v___x_3123_);
lean_dec(v_head_3120_);
v_a_3117_ = v_tail_3121_;
goto _start;
}
else
{
lean_object* v___x_3130_; 
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 1, v_a_3118_);
v___x_3130_ = v___x_3123_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_head_3120_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v_a_3118_);
v___x_3130_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
v_a_3117_ = v_tail_3121_;
v_a_3118_ = v___x_3130_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__5___boxed(lean_object* v_maxPrio_x3f_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__5(v_maxPrio_x3f_3134_, v_a_3135_, v_a_3136_);
lean_dec(v_maxPrio_x3f_3134_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f(lean_object* v_text_3138_, lean_object* v_t_3139_, lean_object* v_hoverPos_3140_){
_start:
{
lean_object* v___x_3141_; lean_object* v_column_3142_; lean_object* v___f_3143_; lean_object* v_gs_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v_maxPrio_x3f_3147_; lean_object* v___x_3148_; 
lean_inc_ref(v_text_3138_);
v___x_3141_ = l_Lean_FileMap_toPosition(v_text_3138_, v_hoverPos_3140_);
v_column_3142_ = lean_ctor_get(v___x_3141_, 1);
lean_inc(v_column_3142_);
lean_dec_ref(v___x_3141_);
v___f_3143_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0___boxed), 7, 3);
lean_closure_set(v___f_3143_, 0, v_text_3138_);
lean_closure_set(v___f_3143_, 1, v_column_3142_);
lean_closure_set(v___f_3143_, 2, v_hoverPos_3140_);
v_gs_3144_ = l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg(v___f_3143_, v_t_3139_);
v___x_3145_ = lean_box(0);
lean_inc(v_gs_3144_);
v___x_3146_ = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2(v_gs_3144_, v___x_3145_);
v_maxPrio_x3f_3147_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(v___x_3146_);
lean_dec(v___x_3146_);
v___x_3148_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__5(v_maxPrio_x3f_3147_, v_gs_3144_, v___x_3145_);
lean_dec(v_maxPrio_x3f_3147_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(lean_object* v___x_3149_, uint8_t v___x_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_){
_start:
{
if (lean_obj_tag(v_a_3151_) == 0)
{
lean_object* v___x_3153_; 
v___x_3153_ = l_List_reverse___redArg(v_a_3152_);
return v___x_3153_;
}
else
{
lean_object* v_head_3154_; lean_object* v_snd_3155_; lean_object* v_tail_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3171_; 
v_head_3154_ = lean_ctor_get(v_a_3151_, 0);
lean_inc(v_head_3154_);
v_snd_3155_ = lean_ctor_get(v_head_3154_, 1);
v_tail_3156_ = lean_ctor_get(v_a_3151_, 1);
v_isSharedCheck_3171_ = !lean_is_exclusive(v_a_3151_);
if (v_isSharedCheck_3171_ == 0)
{
lean_object* v_unused_3172_; 
v_unused_3172_ = lean_ctor_get(v_a_3151_, 0);
lean_dec(v_unused_3172_);
v___x_3158_ = v_a_3151_;
v_isShared_3159_ = v_isSharedCheck_3171_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_tail_3156_);
lean_dec(v_a_3151_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3171_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v_info_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; uint8_t v___x_3164_; 
v_info_3160_ = lean_ctor_get(v_snd_3155_, 1);
v___x_3161_ = l_Lean_Elab_Info_stx(v_info_3160_);
v___x_3162_ = lean_unsigned_to_nat(0u);
v___x_3163_ = l_Lean_Syntax_getArg(v___x_3149_, v___x_3162_);
v___x_3164_ = l_Lean_Syntax_structEq(v___x_3161_, v___x_3163_);
lean_dec(v___x_3163_);
lean_dec(v___x_3161_);
if (v___x_3164_ == 0)
{
if (v___x_3150_ == 0)
{
lean_del_object(v___x_3158_);
lean_dec(v_head_3154_);
v_a_3151_ = v_tail_3156_;
goto _start;
}
else
{
lean_object* v___x_3167_; 
if (v_isShared_3159_ == 0)
{
lean_ctor_set(v___x_3158_, 1, v_a_3152_);
v___x_3167_ = v___x_3158_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_head_3154_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v_a_3152_);
v___x_3167_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
v_a_3151_ = v_tail_3156_;
v_a_3152_ = v___x_3167_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_3158_);
lean_dec(v_head_3154_);
v_a_3151_ = v_tail_3156_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0___boxed(lean_object* v___x_3173_, lean_object* v___x_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_){
_start:
{
uint8_t v___x_1220__boxed_3177_; lean_object* v_res_3178_; 
v___x_1220__boxed_3177_ = lean_unbox(v___x_3174_);
v_res_3178_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(v___x_3173_, v___x_1220__boxed_3177_, v_a_3175_, v_a_3176_);
lean_dec(v___x_3173_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0(lean_object* v_ctx_3185_, lean_object* v_info_3186_, lean_object* v_children_3187_, lean_object* v_results_3188_){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; uint8_t v___x_3191_; 
v___x_3189_ = l_Lean_Elab_Info_stx(v_info_3186_);
v___x_3190_ = ((lean_object*)(l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1));
lean_inc(v___x_3189_);
v___x_3191_ = l_Lean_Syntax_isOfKind(v___x_3189_, v___x_3190_);
if (v___x_3191_ == 0)
{
lean_dec(v___x_3189_);
return v_results_3188_;
}
else
{
lean_object* v___x_3192_; lean_object* v___x_3193_; uint8_t v___x_3194_; 
v___x_3192_ = lean_unsigned_to_nat(0u);
v___x_3193_ = l_Lean_Syntax_getArg(v___x_3189_, v___x_3192_);
v___x_3194_ = l_Lean_Syntax_isIdent(v___x_3193_);
lean_dec(v___x_3193_);
if (v___x_3194_ == 0)
{
lean_dec(v___x_3189_);
return v_results_3188_;
}
else
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = lean_box(0);
v___x_3196_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(v___x_3189_, v___x_3194_, v_results_3188_, v___x_3195_);
lean_dec(v___x_3189_);
return v___x_3196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___boxed(lean_object* v_ctx_3197_, lean_object* v_info_3198_, lean_object* v_children_3199_, lean_object* v_results_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0(v_ctx_3197_, v_info_3198_, v_children_3199_, v_results_3200_);
lean_dec_ref(v_children_3199_);
lean_dec_ref(v_info_3198_);
lean_dec_ref(v_ctx_3197_);
return v_res_3201_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(lean_object* v_x_3202_, lean_object* v_x_3203_){
_start:
{
if (lean_obj_tag(v_x_3202_) == 0)
{
if (lean_obj_tag(v_x_3203_) == 0)
{
uint8_t v___x_3204_; 
v___x_3204_ = 1;
return v___x_3204_;
}
else
{
uint8_t v___x_3205_; 
v___x_3205_ = 0;
return v___x_3205_;
}
}
else
{
if (lean_obj_tag(v_x_3203_) == 0)
{
uint8_t v___x_3206_; 
v___x_3206_ = 0;
return v___x_3206_;
}
else
{
lean_object* v_val_3207_; lean_object* v_val_3208_; uint8_t v___x_3209_; 
v_val_3207_ = lean_ctor_get(v_x_3202_, 0);
v_val_3208_ = lean_ctor_get(v_x_3203_, 0);
v___x_3209_ = l_Lean_Elab_instBEqHoverableInfoPrio_beq(v_val_3207_, v_val_3208_);
return v___x_3209_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4___boxed(lean_object* v_x_3210_, lean_object* v_x_3211_){
_start:
{
uint8_t v_res_3212_; lean_object* v_r_3213_; 
v_res_3212_ = l_instBEqOption_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(v_x_3210_, v_x_3211_);
lean_dec(v_x_3211_);
lean_dec(v_x_3210_);
v_r_3213_ = lean_box(v_res_3212_);
return v_r_3213_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5(lean_object* v_maxPrio_x3f_3214_, lean_object* v_x_3215_){
_start:
{
if (lean_obj_tag(v_x_3215_) == 0)
{
lean_object* v___x_3216_; 
v___x_3216_ = lean_box(0);
return v___x_3216_;
}
else
{
lean_object* v_head_3217_; lean_object* v_tail_3218_; lean_object* v_fst_3219_; lean_object* v___x_3220_; uint8_t v___x_3221_; 
v_head_3217_ = lean_ctor_get(v_x_3215_, 0);
v_tail_3218_ = lean_ctor_get(v_x_3215_, 1);
v_fst_3219_ = lean_ctor_get(v_head_3217_, 0);
lean_inc(v_fst_3219_);
v___x_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3220_, 0, v_fst_3219_);
v___x_3221_ = l_instBEqOption_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(v___x_3220_, v_maxPrio_x3f_3214_);
lean_dec_ref_known(v___x_3220_, 1);
if (v___x_3221_ == 0)
{
v_x_3215_ = v_tail_3218_;
goto _start;
}
else
{
lean_object* v___x_3223_; 
lean_inc(v_head_3217_);
v___x_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3223_, 0, v_head_3217_);
return v___x_3223_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5___boxed(lean_object* v_maxPrio_x3f_3224_, lean_object* v_x_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5(v_maxPrio_x3f_3224_, v_x_3225_);
lean_dec(v_x_3225_);
lean_dec(v_maxPrio_x3f_3224_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(lean_object* v_x_3227_, lean_object* v_x_3228_){
_start:
{
if (lean_obj_tag(v_x_3228_) == 0)
{
lean_inc_ref(v_x_3227_);
return v_x_3227_;
}
else
{
lean_object* v_head_3229_; lean_object* v_tail_3230_; uint8_t v___x_3231_; 
v_head_3229_ = lean_ctor_get(v_x_3228_, 0);
v_tail_3230_ = lean_ctor_get(v_x_3228_, 1);
v___x_3231_ = l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(v_x_3227_, v_head_3229_);
if (v___x_3231_ == 2)
{
v_x_3228_ = v_tail_3230_;
goto _start;
}
else
{
v_x_3227_ = v_head_3229_;
v_x_3228_ = v_tail_3230_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4___boxed(lean_object* v_x_3234_, lean_object* v_x_3235_){
_start:
{
lean_object* v_res_3236_; 
v_res_3236_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(v_x_3234_, v_x_3235_);
lean_dec(v_x_3235_);
lean_dec_ref(v_x_3234_);
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(lean_object* v_x_3237_){
_start:
{
if (lean_obj_tag(v_x_3237_) == 0)
{
lean_object* v___x_3238_; 
v___x_3238_ = lean_box(0);
return v___x_3238_;
}
else
{
lean_object* v_head_3239_; lean_object* v_tail_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v_head_3239_ = lean_ctor_get(v_x_3237_, 0);
v_tail_3240_ = lean_ctor_get(v_x_3237_, 1);
v___x_3241_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(v_head_3239_, v_tail_3240_);
v___x_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3241_);
return v___x_3242_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3___boxed(lean_object* v_x_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(v_x_3243_);
lean_dec(v_x_3243_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__1(lean_object* v_a_3245_, lean_object* v_a_3246_){
_start:
{
if (lean_obj_tag(v_a_3245_) == 0)
{
lean_object* v___x_3247_; 
v___x_3247_ = lean_array_to_list(v_a_3246_);
return v___x_3247_;
}
else
{
lean_object* v_head_3248_; 
v_head_3248_ = lean_ctor_get(v_a_3245_, 0);
if (lean_obj_tag(v_head_3248_) == 0)
{
lean_object* v_tail_3249_; 
v_tail_3249_ = lean_ctor_get(v_a_3245_, 1);
lean_inc(v_tail_3249_);
lean_dec_ref_known(v_a_3245_, 2);
v_a_3245_ = v_tail_3249_;
goto _start;
}
else
{
lean_object* v_val_3251_; 
v_val_3251_ = lean_ctor_get(v_head_3248_, 0);
if (lean_obj_tag(v_val_3251_) == 0)
{
lean_object* v_tail_3252_; 
v_tail_3252_ = lean_ctor_get(v_a_3245_, 1);
lean_inc(v_tail_3252_);
lean_dec_ref_known(v_a_3245_, 2);
v_a_3245_ = v_tail_3252_;
goto _start;
}
else
{
lean_object* v_tail_3254_; lean_object* v_val_3255_; lean_object* v___x_3256_; 
lean_inc_ref(v_val_3251_);
v_tail_3254_ = lean_ctor_get(v_a_3245_, 1);
lean_inc(v_tail_3254_);
lean_dec_ref_known(v_a_3245_, 2);
v_val_3255_ = lean_ctor_get(v_val_3251_, 0);
lean_inc(v_val_3255_);
lean_dec_ref_known(v_val_3251_, 1);
v___x_3256_ = lean_array_push(v_a_3246_, v_val_3255_);
v_a_3245_ = v_tail_3254_;
v_a_3246_ = v___x_3256_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__2(lean_object* v_a_3258_, lean_object* v_a_3259_){
_start:
{
if (lean_obj_tag(v_a_3258_) == 0)
{
lean_object* v___x_3260_; 
v___x_3260_ = l_List_reverse___redArg(v_a_3259_);
return v___x_3260_;
}
else
{
lean_object* v_head_3261_; lean_object* v_tail_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3271_; 
v_head_3261_ = lean_ctor_get(v_a_3258_, 0);
v_tail_3262_ = lean_ctor_get(v_a_3258_, 1);
v_isSharedCheck_3271_ = !lean_is_exclusive(v_a_3258_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3264_ = v_a_3258_;
v_isShared_3265_ = v_isSharedCheck_3271_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_tail_3262_);
lean_inc(v_head_3261_);
lean_dec(v_a_3258_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3271_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v_fst_3266_; lean_object* v___x_3268_; 
v_fst_3266_ = lean_ctor_get(v_head_3261_, 0);
lean_inc(v_fst_3266_);
lean_dec(v_head_3261_);
if (v_isShared_3265_ == 0)
{
lean_ctor_set(v___x_3264_, 1, v_a_3259_);
lean_ctor_set(v___x_3264_, 0, v_fst_3266_);
v___x_3268_ = v___x_3264_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_fst_3266_);
lean_ctor_set(v_reuseFailAlloc_3270_, 1, v_a_3259_);
v___x_3268_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
v_a_3258_ = v_tail_3262_;
v_a_3259_ = v___x_3268_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1(lean_object* v_filter_3272_, lean_object* v_hoverPos_3273_, uint8_t v_includeStop_3274_, lean_object* v_ctx_3275_, lean_object* v_info_3276_, lean_object* v_children_3277_, lean_object* v_results_3278_){
_start:
{
uint8_t v___y_3280_; uint8_t v___y_3281_; lean_object* v___y_3282_; uint8_t v___y_3283_; uint8_t v___y_3289_; uint8_t v___y_3290_; uint8_t v___y_3291_; lean_object* v___y_3292_; uint8_t v___y_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v_maxPrio_x3f_3299_; lean_object* v_bestResult_x3f_3300_; 
v___x_3294_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___closed__0));
v___x_3295_ = l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__1(v_results_3278_, v___x_3294_);
lean_inc_ref(v_children_3277_);
lean_inc_ref(v_info_3276_);
lean_inc_ref(v_ctx_3275_);
v___x_3296_ = lean_apply_4(v_filter_3272_, v_ctx_3275_, v_info_3276_, v_children_3277_, v___x_3295_);
v___x_3297_ = lean_box(0);
lean_inc(v___x_3296_);
v___x_3298_ = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__2(v___x_3296_, v___x_3297_);
v_maxPrio_x3f_3299_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(v___x_3298_);
lean_dec(v___x_3298_);
v_bestResult_x3f_3300_ = l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5(v_maxPrio_x3f_3299_, v___x_3296_);
lean_dec(v___x_3296_);
lean_dec(v_maxPrio_x3f_3299_);
if (lean_obj_tag(v_bestResult_x3f_3300_) == 1)
{
lean_dec_ref(v_children_3277_);
lean_dec_ref(v_info_3276_);
lean_dec_ref(v_ctx_3275_);
return v_bestResult_x3f_3300_;
}
else
{
lean_object* v___x_3301_; uint8_t v___y_3303_; uint8_t v___y_3304_; uint8_t v___y_3305_; uint8_t v___y_3320_; lean_object* v___x_3323_; uint8_t v___x_3324_; 
lean_dec(v_bestResult_x3f_3300_);
v___x_3301_ = l_Lean_Elab_Info_stx(v_info_3276_);
v___x_3323_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__1));
lean_inc(v___x_3301_);
v___x_3324_ = l_Lean_Syntax_isOfKind(v___x_3301_, v___x_3323_);
if (v___x_3324_ == 0)
{
lean_object* v___x_3325_; 
lean_inc_ref(v_info_3276_);
v___x_3325_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_3276_);
if (lean_obj_tag(v___x_3325_) == 0)
{
v___y_3320_ = v___x_3324_;
goto v___jp_3319_;
}
else
{
lean_object* v_val_3326_; lean_object* v_elaborator_3327_; lean_object* v___x_3328_; uint8_t v___x_3329_; 
v_val_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc(v_val_3326_);
lean_dec_ref_known(v___x_3325_, 1);
v_elaborator_3327_ = lean_ctor_get(v_val_3326_, 0);
lean_inc(v_elaborator_3327_);
lean_dec(v_val_3326_);
v___x_3328_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6));
v___x_3329_ = lean_name_eq(v_elaborator_3327_, v___x_3328_);
lean_dec(v_elaborator_3327_);
if (v___x_3329_ == 0)
{
v___y_3320_ = v___x_3329_;
goto v___jp_3319_;
}
else
{
lean_object* v___x_3330_; 
lean_dec(v___x_3301_);
lean_dec_ref(v_children_3277_);
lean_dec_ref(v_info_3276_);
lean_dec_ref(v_ctx_3275_);
v___x_3330_ = lean_box(0);
return v___x_3330_;
}
}
}
else
{
lean_object* v___x_3331_; 
lean_dec(v___x_3301_);
lean_dec_ref(v_children_3277_);
lean_dec_ref(v_info_3276_);
lean_dec_ref(v_ctx_3275_);
v___x_3331_ = lean_box(0);
return v___x_3331_;
}
v___jp_3302_:
{
lean_object* v___x_3306_; 
v___x_3306_ = l_Lean_Syntax_getRange_x3f(v___x_3301_, v___y_3304_);
lean_dec(v___x_3301_);
if (lean_obj_tag(v___x_3306_) == 1)
{
lean_object* v_val_3307_; uint8_t v___x_3308_; 
v_val_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_val_3307_);
lean_dec_ref_known(v___x_3306_, 1);
v___x_3308_ = l_Lean_Syntax_Range_contains(v_val_3307_, v_hoverPos_3273_, v_includeStop_3274_);
if (v___x_3308_ == 0)
{
lean_object* v___x_3309_; 
lean_dec(v_val_3307_);
lean_dec_ref(v_children_3277_);
lean_dec_ref(v_info_3276_);
lean_dec_ref(v_ctx_3275_);
v___x_3309_ = lean_box(0);
return v___x_3309_;
}
else
{
if (v___y_3303_ == 0)
{
if (v___y_3305_ == 0)
{
lean_object* v___x_3310_; 
lean_dec(v_val_3307_);
lean_dec_ref(v_children_3277_);
lean_dec_ref(v_info_3276_);
lean_dec_ref(v_ctx_3275_);
v___x_3310_ = lean_box(0);
return v___x_3310_;
}
else
{
lean_object* v_start_3311_; lean_object* v_stop_3312_; uint8_t v_decide_3313_; lean_object* v___x_3314_; 
v_start_3311_ = lean_ctor_get(v_val_3307_, 0);
lean_inc(v_start_3311_);
v_stop_3312_ = lean_ctor_get(v_val_3307_, 1);
lean_inc(v_stop_3312_);
lean_dec(v_val_3307_);
v_decide_3313_ = lean_nat_dec_eq(v_stop_3312_, v_hoverPos_3273_);
v___x_3314_ = lean_nat_sub(v_stop_3312_, v_start_3311_);
lean_dec(v_start_3311_);
lean_dec(v_stop_3312_);
if (lean_obj_tag(v_info_3276_) == 1)
{
lean_object* v_i_3315_; lean_object* v_expr_3316_; 
v_i_3315_ = lean_ctor_get(v_info_3276_, 0);
v_expr_3316_ = lean_ctor_get(v_i_3315_, 3);
if (lean_obj_tag(v_expr_3316_) == 1)
{
v___y_3289_ = v___y_3303_;
v___y_3290_ = v_decide_3313_;
v___y_3291_ = v___y_3304_;
v___y_3292_ = v___x_3314_;
v___y_3293_ = v___y_3304_;
goto v___jp_3288_;
}
else
{
v___y_3289_ = v___y_3303_;
v___y_3290_ = v_decide_3313_;
v___y_3291_ = v___y_3304_;
v___y_3292_ = v___x_3314_;
v___y_3293_ = v___y_3303_;
goto v___jp_3288_;
}
}
else
{
v___y_3289_ = v___y_3303_;
v___y_3290_ = v_decide_3313_;
v___y_3291_ = v___y_3304_;
v___y_3292_ = v___x_3314_;
v___y_3293_ = v___y_3303_;
goto v___jp_3288_;
}
}
}
else
{
lean_object* v___x_3317_; 
lean_dec(v_val_3307_);
lean_dec_ref(v_children_3277_);
lean_dec_ref(v_info_3276_);
lean_dec_ref(v_ctx_3275_);
v___x_3317_ = lean_box(0);
return v___x_3317_;
}
}
}
else
{
lean_object* v___x_3318_; 
lean_dec(v___x_3306_);
lean_dec_ref(v_children_3277_);
lean_dec_ref(v_info_3276_);
lean_dec_ref(v_ctx_3275_);
v___x_3318_ = lean_box(0);
return v___x_3318_;
}
}
v___jp_3319_:
{
uint8_t v___x_3321_; 
v___x_3321_ = 1;
switch(lean_obj_tag(v_info_3276_))
{
case 7:
{
v___y_3303_ = v___y_3320_;
v___y_3304_ = v___x_3321_;
v___y_3305_ = v___x_3321_;
goto v___jp_3302_;
}
case 5:
{
v___y_3303_ = v___y_3320_;
v___y_3304_ = v___x_3321_;
v___y_3305_ = v___x_3321_;
goto v___jp_3302_;
}
case 6:
{
v___y_3303_ = v___y_3320_;
v___y_3304_ = v___x_3321_;
v___y_3305_ = v___x_3321_;
goto v___jp_3302_;
}
default: 
{
if (v___y_3320_ == 0)
{
lean_object* v___x_3322_; 
lean_inc_ref(v_info_3276_);
v___x_3322_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_3276_);
if (lean_obj_tag(v___x_3322_) == 0)
{
v___y_3303_ = v___y_3320_;
v___y_3304_ = v___x_3321_;
v___y_3305_ = v___y_3320_;
goto v___jp_3302_;
}
else
{
lean_dec_ref_known(v___x_3322_, 1);
v___y_3303_ = v___y_3320_;
v___y_3304_ = v___x_3321_;
v___y_3305_ = v___x_3321_;
goto v___jp_3302_;
}
}
else
{
v___y_3303_ = v___y_3320_;
v___y_3304_ = v___x_3321_;
v___y_3305_ = v___y_3320_;
goto v___jp_3302_;
}
}
}
}
}
v___jp_3279_:
{
lean_object* v_priority_3284_; lean_object* v_result_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v_priority_3284_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_priority_3284_, 0, v___y_3282_);
lean_ctor_set_uint8(v_priority_3284_, sizeof(void*)*1, v___y_3280_);
lean_ctor_set_uint8(v_priority_3284_, sizeof(void*)*1 + 1, v___y_3281_);
lean_ctor_set_uint8(v_priority_3284_, sizeof(void*)*1 + 2, v___y_3283_);
v_result_3285_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_result_3285_, 0, v_ctx_3275_);
lean_ctor_set(v_result_3285_, 1, v_info_3276_);
lean_ctor_set(v_result_3285_, 2, v_children_3277_);
v___x_3286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3286_, 0, v_priority_3284_);
lean_ctor_set(v___x_3286_, 1, v_result_3285_);
v___x_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3286_);
return v___x_3287_;
}
v___jp_3288_:
{
if (lean_obj_tag(v_info_3276_) == 2)
{
v___y_3280_ = v___y_3290_;
v___y_3281_ = v___y_3293_;
v___y_3282_ = v___y_3292_;
v___y_3283_ = v___y_3291_;
goto v___jp_3279_;
}
else
{
v___y_3280_ = v___y_3290_;
v___y_3281_ = v___y_3293_;
v___y_3282_ = v___y_3292_;
v___y_3283_ = v___y_3289_;
goto v___jp_3279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1___boxed(lean_object* v_filter_3332_, lean_object* v_hoverPos_3333_, lean_object* v_includeStop_3334_, lean_object* v_ctx_3335_, lean_object* v_info_3336_, lean_object* v_children_3337_, lean_object* v_results_3338_){
_start:
{
uint8_t v_includeStop_boxed_3339_; lean_object* v_res_3340_; 
v_includeStop_boxed_3339_ = lean_unbox(v_includeStop_3334_);
v_res_3340_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1(v_filter_3332_, v_hoverPos_3333_, v_includeStop_boxed_3339_, v_ctx_3335_, v_info_3336_, v_children_3337_, v_results_3338_);
lean_dec(v_hoverPos_3333_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(lean_object* v_t_3341_, lean_object* v_hoverPos_3342_, uint8_t v_includeStop_3343_, lean_object* v_filter_3344_){
_start:
{
lean_object* v___f_3345_; lean_object* v___x_3346_; lean_object* v_postNode_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___f_3345_ = ((lean_object*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___closed__0));
v___x_3346_ = lean_box(v_includeStop_3343_);
v_postNode_3347_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1___boxed), 7, 3);
lean_closure_set(v_postNode_3347_, 0, v_filter_3344_);
lean_closure_set(v_postNode_3347_, 1, v_hoverPos_3342_);
lean_closure_set(v_postNode_3347_, 2, v___x_3346_);
v___x_3348_ = lean_box(0);
v___x_3349_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v___f_3345_, v_postNode_3347_, v___x_3348_, v_t_3341_);
if (lean_obj_tag(v___x_3349_) == 0)
{
return v___x_3348_;
}
else
{
lean_object* v_val_3350_; 
v_val_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_val_3350_);
lean_dec_ref_known(v___x_3349_, 1);
if (lean_obj_tag(v_val_3350_) == 0)
{
return v___x_3348_;
}
else
{
lean_object* v_val_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3363_; 
v_val_3351_ = lean_ctor_get(v_val_3350_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v_val_3350_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3353_ = v_val_3350_;
v_isShared_3354_ = v_isSharedCheck_3363_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_val_3351_);
lean_dec(v_val_3350_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3363_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v_snd_3355_; lean_object* v_info_3356_; lean_object* v___x_3358_; 
v_snd_3355_ = lean_ctor_get(v_val_3351_, 1);
lean_inc(v_snd_3355_);
lean_dec(v_val_3351_);
v_info_3356_ = lean_ctor_get(v_snd_3355_, 1);
lean_inc_ref(v_info_3356_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 0, v_snd_3355_);
v___x_3358_ = v___x_3353_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_snd_3355_);
v___x_3358_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
if (lean_obj_tag(v_info_3356_) == 1)
{
lean_object* v_i_3359_; lean_object* v_expr_3360_; uint8_t v___x_3361_; 
v_i_3359_ = lean_ctor_get(v_info_3356_, 0);
lean_inc_ref(v_i_3359_);
lean_dec_ref_known(v_info_3356_, 1);
v_expr_3360_ = lean_ctor_get(v_i_3359_, 3);
lean_inc_ref(v_expr_3360_);
lean_dec_ref(v_i_3359_);
v___x_3361_ = l_Lean_Expr_isSyntheticSorry(v_expr_3360_);
lean_dec_ref(v_expr_3360_);
if (v___x_3361_ == 0)
{
return v___x_3358_;
}
else
{
lean_dec_ref(v___x_3358_);
return v___x_3348_;
}
}
else
{
lean_dec_ref(v_info_3356_);
return v___x_3358_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___boxed(lean_object* v_t_3364_, lean_object* v_hoverPos_3365_, lean_object* v_includeStop_3366_, lean_object* v_filter_3367_){
_start:
{
uint8_t v_includeStop_boxed_3368_; lean_object* v_res_3369_; 
v_includeStop_boxed_3368_ = lean_unbox(v_includeStop_3366_);
v_res_3369_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(v_t_3364_, v_hoverPos_3365_, v_includeStop_boxed_3368_, v_filter_3367_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f(lean_object* v_t_3371_, lean_object* v_hoverPos_3372_){
_start:
{
lean_object* v_filter_3373_; uint8_t v___x_3374_; lean_object* v___x_3375_; 
v_filter_3373_ = ((lean_object*)(l_Lean_Elab_InfoTree_termGoalAt_x3f___closed__0));
v___x_3374_ = 1;
v___x_3375_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(v_t_3371_, v_hoverPos_3372_, v___x_3374_, v_filter_3373_);
return v___x_3375_;
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
