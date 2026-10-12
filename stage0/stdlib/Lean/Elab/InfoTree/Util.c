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
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__27;
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
lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1(lean_object* v_postNode_64_, lean_object* v_val_65_, lean_object* v_i_66_, lean_object* v_children_67_, lean_object* v_toBind_68_, lean_object* v___f_69_, lean_object* v_x_70_, lean_object* v_inst_71_, lean_object* v_preNode_72_, lean_object* v___f_73_, uint8_t v_visitChildren_74_){
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
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_postNode_64_ = stack[0].m_obj;
lean_object* v_val_65_ = stack[1].m_obj;
lean_object* v_i_66_ = stack[2].m_obj;
lean_object* v_children_67_ = stack[3].m_obj;
lean_object* v_toBind_68_ = stack[4].m_obj;
lean_object* v___f_69_ = stack[5].m_obj;
lean_object* v_x_70_ = stack[6].m_obj;
lean_object* v_inst_71_ = stack[7].m_obj;
lean_object* v_preNode_72_ = stack[8].m_obj;
lean_object* v___f_73_ = stack[9].m_obj;
uint8_t v_visitChildren_74_ = stack[10].m_num;
lean_object* v_res_84_;
v_res_84_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___lam__1(v_postNode_64_, v_val_65_, v_i_66_, v_children_67_, v_toBind_68_, v___f_69_, v_x_70_, v_inst_71_, v_preNode_72_, v___f_73_, v_visitChildren_74_);
stack->m_obj
 = v_res_84_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go(lean_object* v_m_85_, lean_object* v_00_u03b1_86_, lean_object* v_inst_87_, lean_object* v_preNode_88_, lean_object* v_postNode_89_, lean_object* v_x_90_, lean_object* v_x_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_87_, v_preNode_88_, v_postNode_89_, v_x_90_, v_x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM___redArg(lean_object* v_inst_93_, lean_object* v_preNode_94_, lean_object* v_postNode_95_, lean_object* v_ctx_x3f_96_, lean_object* v_x_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_93_, v_preNode_94_, v_postNode_95_, v_ctx_x3f_96_, v_x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM(lean_object* v_m_99_, lean_object* v_00_u03b1_100_, lean_object* v_inst_101_, lean_object* v_preNode_102_, lean_object* v_postNode_103_, lean_object* v_ctx_x3f_104_, lean_object* v_x_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_101_, v_preNode_102_, v_postNode_103_, v_ctx_x3f_104_, v_x_105_);
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
v___x_128_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_119_, v_preNode_120_, v___f_127_, v_ctx_x3f_122_, v_t_123_);
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
v___x_180_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_169_, v___f_178_, v___f_177_, v___x_179_, v_i_171_);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg(lean_object* v_msg_227_){
_start:
{
lean_object* v___f_228_; lean_object* v___f_229_; lean_object* v___f_230_; lean_object* v___f_231_; lean_object* v___f_232_; lean_object* v___f_233_; lean_object* v___f_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___f_228_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__0));
v___f_229_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__1));
v___f_230_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__2));
v___f_231_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__3));
v___f_232_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__4));
v___f_233_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__5));
v___f_234_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg___closed__6));
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(lean_object* v_preNode_241_, lean_object* v_postNode_242_, lean_object* v_x_243_, lean_object* v_x_244_){
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
v___x_249_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg___closed__3);
v___x_250_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg(v___x_249_);
return v___x_250_;
}
else
{
lean_object* v_i_251_; lean_object* v_children_252_; lean_object* v_val_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
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
if (v___x_255_ == 0)
{
lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_264_; 
lean_dec_ref(v_preNode_241_);
v_isSharedCheck_264_ = !lean_is_exclusive(v_x_243_);
if (v_isSharedCheck_264_ == 0)
{
lean_object* v_unused_265_; 
v_unused_265_ = lean_ctor_get(v_x_243_, 0);
lean_dec(v_unused_265_);
v___x_257_ = v_x_243_;
v_isShared_258_ = v_isSharedCheck_264_;
goto v_resetjp_256_;
}
else
{
lean_dec(v_x_243_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_264_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_259_ = lean_box(0);
v___x_260_ = lean_apply_4(v_postNode_242_, v_val_253_, v_i_251_, v_children_252_, v___x_259_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v___x_260_);
v___x_262_ = v___x_257_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_266_ = l_Lean_Elab_Info_updateContext_x3f(v_x_243_, v_i_251_);
v___x_267_ = l_Lean_PersistentArray_toList___redArg(v_children_252_);
v___x_268_ = lean_box(0);
lean_inc(v_postNode_242_);
v___x_269_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4___redArg(v_preNode_241_, v_postNode_242_, v___x_266_, v___x_267_, v___x_268_);
v___x_270_ = lean_apply_4(v_postNode_242_, v_val_253_, v_i_251_, v_children_252_, v___x_269_);
v___x_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
}
}
default: 
{
lean_object* v___x_272_; 
lean_dec_ref_known(v_x_244_, 1);
lean_dec(v_x_243_);
lean_dec(v_postNode_242_);
lean_dec_ref(v_preNode_241_);
v___x_272_ = lean_box(0);
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4___redArg(lean_object* v_preNode_273_, lean_object* v_postNode_274_, lean_object* v___x_275_, lean_object* v_x_276_, lean_object* v_x_277_){
_start:
{
if (lean_obj_tag(v_x_276_) == 0)
{
lean_object* v___x_278_; 
lean_dec(v___x_275_);
lean_dec(v_postNode_274_);
lean_dec_ref(v_preNode_273_);
v___x_278_ = l_List_reverse___redArg(v_x_277_);
return v___x_278_;
}
else
{
lean_object* v_head_279_; lean_object* v_tail_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_289_; 
v_head_279_ = lean_ctor_get(v_x_276_, 0);
v_tail_280_ = lean_ctor_get(v_x_276_, 1);
v_isSharedCheck_289_ = !lean_is_exclusive(v_x_276_);
if (v_isSharedCheck_289_ == 0)
{
v___x_282_ = v_x_276_;
v_isShared_283_ = v_isSharedCheck_289_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_tail_280_);
lean_inc(v_head_279_);
lean_dec(v_x_276_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_289_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v___x_286_; 
lean_inc(v___x_275_);
lean_inc(v_postNode_274_);
lean_inc_ref(v_preNode_273_);
v___x_284_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v_preNode_273_, v_postNode_274_, v___x_275_, v_head_279_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 1, v_x_277_);
lean_ctor_set(v___x_282_, 0, v___x_284_);
v___x_286_ = v___x_282_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_x_277_);
v___x_286_ = v_reuseFailAlloc_288_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
v_x_276_ = v_tail_280_;
v_x_277_ = v___x_286_;
goto _start;
}
}
}
}
}
uint8_t l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__1(lean_object* v_x_290_, lean_object* v_x_291_, lean_object* v_x_292_){
_start:
{
uint8_t v___x_293_; 
v___x_293_ = 1;
return v___x_293_;
}
}
LEAN_EXPORT void l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_290_ = stack[0].m_obj;
lean_object* v_x_291_ = stack[1].m_obj;
lean_object* v_x_292_ = stack[2].m_obj;
uint8_t v_res_294_;
v_res_294_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___lam__1(v_x_290_, v_x_291_, v_x_292_);
stack->m_num = v_res_294_;
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
v___x_306_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v___f_304_, v___f_303_, v___x_305_, v_i_302_);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_329_, lean_object* v_msg_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__3___redArg(v_msg_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2(lean_object* v_00_u03b1_332_, lean_object* v_preNode_333_, lean_object* v_postNode_334_, lean_object* v_x_335_, lean_object* v_x_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v_preNode_333_, v_postNode_334_, v_x_335_, v_x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_338_, lean_object* v_preNode_339_, lean_object* v_postNode_340_, lean_object* v___x_341_, lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2_spec__4___redArg(v_preNode_339_, v_postNode_340_, v___x_341_, v_x_342_, v_x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0(lean_object* v_toPure_345_, lean_object* v_____do__lift_346_){
_start:
{
if (lean_obj_tag(v_____do__lift_346_) == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_box(0);
v___x_348_ = lean_apply_2(v_toPure_345_, lean_box(0), v___x_347_);
return v___x_348_;
}
else
{
lean_object* v_val_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_val_349_ = lean_ctor_get(v_____do__lift_346_, 0);
v___x_350_ = lean_box(0);
lean_inc(v_val_349_);
v___x_351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_351_, 0, v_val_349_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
v___x_352_ = lean_apply_2(v_toPure_345_, lean_box(0), v___x_351_);
return v___x_352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0___boxed(lean_object* v_toPure_353_, lean_object* v_____do__lift_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0(v_toPure_353_, v_____do__lift_354_);
lean_dec(v_____do__lift_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__1(lean_object* v_toPure_356_, lean_object* v_p_357_, lean_object* v_toBind_358_, lean_object* v___f_359_, lean_object* v_ctx_360_, lean_object* v_i_361_, lean_object* v_cs_362_, lean_object* v_rs_363_){
_start:
{
uint8_t v___x_364_; 
v___x_364_ = l_List_isEmpty___redArg(v_rs_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
lean_dec_ref(v_cs_362_);
lean_dec_ref(v_i_361_);
lean_dec_ref(v_ctx_360_);
lean_dec(v___f_359_);
lean_dec(v_toBind_358_);
lean_dec(v_p_357_);
v___x_365_ = lean_apply_2(v_toPure_356_, lean_box(0), v_rs_363_);
return v___x_365_;
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; 
lean_dec(v_rs_363_);
lean_dec(v_toPure_356_);
v___x_366_ = lean_apply_3(v_p_357_, v_ctx_360_, v_i_361_, v_cs_362_);
v___x_367_ = lean_apply_4(v_toBind_358_, lean_box(0), lean_box(0), v___x_366_, v___f_359_);
return v___x_367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___redArg(lean_object* v_inst_368_, lean_object* v_p_369_, lean_object* v_infoTree_370_){
_start:
{
lean_object* v_toApplicative_371_; lean_object* v_toBind_372_; lean_object* v_toPure_373_; lean_object* v___f_374_; lean_object* v___f_375_; lean_object* v___x_376_; 
v_toApplicative_371_ = lean_ctor_get(v_inst_368_, 0);
v_toBind_372_ = lean_ctor_get(v_inst_368_, 1);
v_toPure_373_ = lean_ctor_get(v_toApplicative_371_, 1);
lean_inc_n(v_toPure_373_, 2);
v___f_374_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_374_, 0, v_toPure_373_);
lean_inc(v_toBind_372_);
v___f_375_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_deepestNodesM___redArg___lam__1), 8, 4);
lean_closure_set(v___f_375_, 0, v_toPure_373_);
lean_closure_set(v___f_375_, 1, v_p_369_);
lean_closure_set(v___f_375_, 2, v_toBind_372_);
lean_closure_set(v___f_375_, 3, v___f_374_);
v___x_376_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg(v_inst_368_, v___f_375_, v_infoTree_370_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM(lean_object* v_m_377_, lean_object* v_00_u03b1_378_, lean_object* v_inst_379_, lean_object* v_p_380_, lean_object* v_infoTree_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Elab_InfoTree_deepestNodesM___redArg(v_inst_379_, v_p_380_, v_infoTree_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodes___redArg___lam__0(lean_object* v_p_383_, lean_object* v_x1_384_, lean_object* v_x2_385_, lean_object* v_x3_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = lean_apply_3(v_p_383_, v_x1_384_, v_x2_385_, v_x3_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0(lean_object* v_p_388_, lean_object* v_ctx_389_, lean_object* v_i_390_, lean_object* v_cs_391_, lean_object* v_rs_392_){
_start:
{
uint8_t v___x_393_; 
v___x_393_ = l_List_isEmpty___redArg(v_rs_392_);
if (v___x_393_ == 0)
{
lean_dec_ref(v_cs_391_);
lean_dec_ref(v_i_390_);
lean_dec_ref(v_ctx_389_);
lean_dec_ref(v_p_388_);
lean_inc(v_rs_392_);
return v_rs_392_;
}
else
{
lean_object* v___x_394_; 
v___x_394_ = lean_apply_3(v_p_388_, v_ctx_389_, v_i_390_, v_cs_391_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v___x_395_; 
v___x_395_ = lean_box(0);
return v___x_395_;
}
else
{
lean_object* v_val_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_val_396_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_val_396_);
lean_dec_ref_known(v___x_394_, 1);
v___x_397_ = lean_box(0);
v___x_398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_398_, 0, v_val_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
return v___x_398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0___boxed(lean_object* v_p_399_, lean_object* v_ctx_400_, lean_object* v_i_401_, lean_object* v_cs_402_, lean_object* v_rs_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0(v_p_399_, v_ctx_400_, v_i_401_, v_cs_402_, v_rs_403_);
lean_dec(v_rs_403_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg(lean_object* v_p_405_, lean_object* v_infoTree_406_){
_start:
{
lean_object* v___f_407_; lean_object* v___x_408_; 
v___f_407_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_407_, 0, v_p_405_);
v___x_408_ = l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg(v___f_407_, v_infoTree_406_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodes___redArg(lean_object* v_p_409_, lean_object* v_infoTree_410_){
_start:
{
lean_object* v___f_411_; lean_object* v___x_412_; 
v___f_411_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_deepestNodes___redArg___lam__0), 4, 1);
lean_closure_set(v___f_411_, 0, v_p_409_);
v___x_412_ = l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg(v___f_411_, v_infoTree_410_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodes(lean_object* v_00_u03b1_413_, lean_object* v_p_414_, lean_object* v_infoTree_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v_p_414_, v_infoTree_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0(lean_object* v_00_u03b1_417_, lean_object* v_p_418_, lean_object* v_infoTree_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_Elab_InfoTree_deepestNodesM___at___00Lean_Elab_InfoTree_deepestNodes_spec__0___redArg(v_p_418_, v_infoTree_419_);
return v___x_420_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(lean_object* v_f_422_, lean_object* v___x_423_, lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
if (lean_obj_tag(v_x_424_) == 0)
{
lean_object* v_cs_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_cs_426_ = lean_ctor_get(v_x_424_, 0);
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = lean_array_get_size(v_cs_426_);
v___x_429_ = lean_nat_dec_lt(v___x_427_, v___x_428_);
if (v___x_429_ == 0)
{
lean_dec(v___x_423_);
lean_dec(v_f_422_);
return v_x_425_;
}
else
{
size_t v___x_430_; size_t v___x_431_; lean_object* v___x_432_; 
v___x_430_ = ((size_t)0ULL);
v___x_431_ = lean_usize_of_nat(v___x_428_);
v___x_432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_422_, v___x_423_, v_cs_426_, v___x_430_, v___x_431_, v_x_425_);
return v___x_432_;
}
}
else
{
lean_object* v_vs_433_; lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v_vs_433_ = lean_ctor_get(v_x_424_, 0);
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = lean_array_get_size(v_vs_433_);
v___x_436_ = lean_nat_dec_lt(v___x_434_, v___x_435_);
if (v___x_436_ == 0)
{
lean_dec(v___x_423_);
lean_dec(v_f_422_);
return v_x_425_;
}
else
{
size_t v___x_437_; size_t v___x_438_; lean_object* v___x_439_; 
v___x_437_ = ((size_t)0ULL);
v___x_438_ = lean_usize_of_nat(v___x_435_);
v___x_439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_422_, v___x_423_, v_vs_433_, v___x_437_, v___x_438_, v_x_425_);
return v___x_439_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(lean_object* v_f_440_, lean_object* v___x_441_, lean_object* v_as_442_, size_t v_i_443_, size_t v_stop_444_, lean_object* v_b_445_){
_start:
{
uint8_t v___x_446_; 
v___x_446_ = lean_usize_dec_eq(v_i_443_, v_stop_444_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; size_t v___x_449_; size_t v___x_450_; 
v___x_447_ = lean_array_uget_borrowed(v_as_442_, v_i_443_);
lean_inc(v___x_441_);
lean_inc(v_f_440_);
v___x_448_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(v_f_440_, v___x_441_, v___x_447_, v_b_445_);
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_add(v_i_443_, v___x_449_);
v_i_443_ = v___x_450_;
v_b_445_ = v___x_448_;
goto _start;
}
else
{
lean_dec(v___x_441_);
lean_dec(v_f_440_);
return v_b_445_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_440_ = stack[0].m_obj;
lean_object* v___x_441_ = stack[1].m_obj;
lean_object* v_as_442_ = stack[2].m_obj;
size_t v_i_443_ = stack[3].m_num;
size_t v_stop_444_ = stack[4].m_num;
lean_object* v_b_445_ = stack[5].m_obj;
lean_object* v_res_452_;
v_res_452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_440_, v___x_441_, v_as_442_, v_i_443_, v_stop_444_, v_b_445_);
stack->m_obj
 = v_res_452_;
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(lean_object* v_f_453_, lean_object* v___x_454_, lean_object* v_x_455_, size_t v_x_456_, size_t v_x_457_, lean_object* v_x_458_){
_start:
{
if (lean_obj_tag(v_x_455_) == 0)
{
lean_object* v_cs_459_; lean_object* v___x_460_; size_t v___x_461_; lean_object* v_j_462_; lean_object* v___x_463_; size_t v___x_464_; size_t v___x_465_; size_t v___x_466_; size_t v___x_467_; size_t v___x_468_; size_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v_cs_459_ = lean_ctor_get(v_x_455_, 0);
v___x_460_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0);
v___x_461_ = lean_usize_shift_right(v_x_456_, v_x_457_);
v_j_462_ = lean_usize_to_nat(v___x_461_);
v___x_463_ = lean_array_get_borrowed(v___x_460_, v_cs_459_, v_j_462_);
v___x_464_ = ((size_t)1ULL);
v___x_465_ = lean_usize_shift_left(v___x_464_, v_x_457_);
v___x_466_ = lean_usize_sub(v___x_465_, v___x_464_);
v___x_467_ = lean_usize_land(v_x_456_, v___x_466_);
v___x_468_ = ((size_t)5ULL);
v___x_469_ = lean_usize_sub(v_x_457_, v___x_468_);
lean_inc(v___x_454_);
lean_inc(v_f_453_);
v___x_470_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(v_f_453_, v___x_454_, v___x_463_, v___x_467_, v___x_469_, v_x_458_);
v___x_471_ = lean_unsigned_to_nat(1u);
v___x_472_ = lean_nat_add(v_j_462_, v___x_471_);
lean_dec(v_j_462_);
v___x_473_ = lean_array_get_size(v_cs_459_);
v___x_474_ = lean_nat_dec_lt(v___x_472_, v___x_473_);
if (v___x_474_ == 0)
{
lean_dec(v___x_472_);
lean_dec(v___x_454_);
lean_dec(v_f_453_);
return v___x_470_;
}
else
{
size_t v___x_475_; size_t v___x_476_; lean_object* v___x_477_; 
v___x_475_ = lean_usize_of_nat(v___x_472_);
lean_dec(v___x_472_);
v___x_476_ = lean_usize_of_nat(v___x_473_);
v___x_477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_453_, v___x_454_, v_cs_459_, v___x_475_, v___x_476_, v___x_470_);
return v___x_477_;
}
}
else
{
lean_object* v_vs_478_; lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v_vs_478_ = lean_ctor_get(v_x_455_, 0);
v___x_479_ = lean_usize_to_nat(v_x_456_);
v___x_480_ = lean_array_get_size(v_vs_478_);
v___x_481_ = lean_nat_dec_lt(v___x_479_, v___x_480_);
if (v___x_481_ == 0)
{
lean_dec(v___x_479_);
lean_dec(v___x_454_);
lean_dec(v_f_453_);
return v_x_458_;
}
else
{
size_t v___x_482_; size_t v___x_483_; lean_object* v___x_484_; 
v___x_482_ = lean_usize_of_nat(v___x_479_);
lean_dec(v___x_479_);
v___x_483_ = lean_usize_of_nat(v___x_480_);
v___x_484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_453_, v___x_454_, v_vs_478_, v___x_482_, v___x_483_, v_x_458_);
return v___x_484_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_453_ = stack[0].m_obj;
lean_object* v___x_454_ = stack[1].m_obj;
lean_object* v_x_455_ = stack[2].m_obj;
size_t v_x_456_ = stack[3].m_num;
size_t v_x_457_ = stack[4].m_num;
lean_object* v_x_458_ = stack[5].m_obj;
lean_object* v_res_485_;
v_res_485_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(v_f_453_, v___x_454_, v_x_455_, v_x_456_, v_x_457_, v_x_458_);
stack->m_obj
 = v_res_485_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(lean_object* v_f_486_, lean_object* v___x_487_, lean_object* v_t_488_, lean_object* v_init_489_, lean_object* v_start_490_){
_start:
{
lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_491_ = lean_unsigned_to_nat(0u);
v___x_492_ = lean_nat_dec_eq(v_start_490_, v___x_491_);
if (v___x_492_ == 0)
{
lean_object* v_root_493_; lean_object* v_tail_494_; size_t v_shift_495_; lean_object* v_tailOff_496_; uint8_t v___x_497_; 
v_root_493_ = lean_ctor_get(v_t_488_, 0);
v_tail_494_ = lean_ctor_get(v_t_488_, 1);
v_shift_495_ = lean_ctor_get_usize(v_t_488_, 4);
v_tailOff_496_ = lean_ctor_get(v_t_488_, 3);
v___x_497_ = lean_nat_dec_le(v_tailOff_496_, v_start_490_);
if (v___x_497_ == 0)
{
size_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_498_ = lean_usize_of_nat(v_start_490_);
lean_inc(v___x_487_);
lean_inc(v_f_486_);
v___x_499_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(v_f_486_, v___x_487_, v_root_493_, v___x_498_, v_shift_495_, v_init_489_);
v___x_500_ = lean_array_get_size(v_tail_494_);
v___x_501_ = lean_nat_dec_lt(v___x_491_, v___x_500_);
if (v___x_501_ == 0)
{
lean_dec(v___x_487_);
lean_dec(v_f_486_);
return v___x_499_;
}
else
{
size_t v___x_502_; size_t v___x_503_; lean_object* v___x_504_; 
v___x_502_ = ((size_t)0ULL);
v___x_503_ = lean_usize_of_nat(v___x_500_);
v___x_504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_486_, v___x_487_, v_tail_494_, v___x_502_, v___x_503_, v___x_499_);
return v___x_504_;
}
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_505_ = lean_nat_sub(v_start_490_, v_tailOff_496_);
v___x_506_ = lean_array_get_size(v_tail_494_);
v___x_507_ = lean_nat_dec_lt(v___x_505_, v___x_506_);
if (v___x_507_ == 0)
{
lean_dec(v___x_505_);
lean_dec(v___x_487_);
lean_dec(v_f_486_);
return v_init_489_;
}
else
{
size_t v___x_508_; size_t v___x_509_; lean_object* v___x_510_; 
v___x_508_ = lean_usize_of_nat(v___x_505_);
lean_dec(v___x_505_);
v___x_509_ = lean_usize_of_nat(v___x_506_);
v___x_510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_486_, v___x_487_, v_tail_494_, v___x_508_, v___x_509_, v_init_489_);
return v___x_510_;
}
}
}
else
{
lean_object* v_root_511_; lean_object* v_tail_512_; lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v_root_511_ = lean_ctor_get(v_t_488_, 0);
v_tail_512_ = lean_ctor_get(v_t_488_, 1);
lean_inc(v___x_487_);
lean_inc(v_f_486_);
v___x_513_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(v_f_486_, v___x_487_, v_root_511_, v_init_489_);
v___x_514_ = lean_array_get_size(v_tail_512_);
v___x_515_ = lean_nat_dec_lt(v___x_491_, v___x_514_);
if (v___x_515_ == 0)
{
lean_dec(v___x_487_);
lean_dec(v_f_486_);
return v___x_513_;
}
else
{
size_t v___x_516_; size_t v___x_517_; lean_object* v___x_518_; 
v___x_516_ = ((size_t)0ULL);
v___x_517_ = lean_usize_of_nat(v___x_514_);
v___x_518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_486_, v___x_487_, v_tail_512_, v___x_516_, v___x_517_, v___x_513_);
return v___x_518_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go___redArg(lean_object* v_f_519_, lean_object* v_ctx_x3f_520_, lean_object* v_a_521_, lean_object* v_x_522_){
_start:
{
switch(lean_obj_tag(v_x_522_))
{
case 0:
{
lean_object* v_i_523_; lean_object* v_t_524_; lean_object* v___x_525_; 
v_i_523_ = lean_ctor_get(v_x_522_, 0);
lean_inc_ref(v_i_523_);
v_t_524_ = lean_ctor_get(v_x_522_, 1);
lean_inc_ref(v_t_524_);
lean_dec_ref_known(v_x_522_, 2);
v___x_525_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_523_, v_ctx_x3f_520_);
v_ctx_x3f_520_ = v___x_525_;
v_x_522_ = v_t_524_;
goto _start;
}
case 1:
{
lean_object* v_i_527_; lean_object* v_children_528_; lean_object* v___y_530_; 
v_i_527_ = lean_ctor_get(v_x_522_, 0);
lean_inc_ref(v_i_527_);
v_children_528_ = lean_ctor_get(v_x_522_, 1);
lean_inc_ref(v_children_528_);
lean_dec_ref_known(v_x_522_, 2);
if (lean_obj_tag(v_ctx_x3f_520_) == 0)
{
v___y_530_ = v_a_521_;
goto v___jp_529_;
}
else
{
lean_object* v_val_534_; lean_object* v___x_535_; 
v_val_534_ = lean_ctor_get(v_ctx_x3f_520_, 0);
lean_inc(v_f_519_);
lean_inc_ref(v_i_527_);
lean_inc(v_val_534_);
v___x_535_ = lean_apply_3(v_f_519_, v_val_534_, v_i_527_, v_a_521_);
v___y_530_ = v___x_535_;
goto v___jp_529_;
}
v___jp_529_:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_531_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_520_, v_i_527_);
lean_dec_ref(v_i_527_);
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(v_f_519_, v___x_531_, v_children_528_, v___y_530_, v___x_532_);
lean_dec_ref(v_children_528_);
return v___x_533_;
}
}
default: 
{
lean_dec_ref_known(v_x_522_, 1);
lean_dec(v_ctx_x3f_520_);
lean_dec(v_f_519_);
return v_a_521_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(lean_object* v_f_536_, lean_object* v___x_537_, lean_object* v_as_538_, size_t v_i_539_, size_t v_stop_540_, lean_object* v_b_541_){
_start:
{
uint8_t v___x_542_; 
v___x_542_ = lean_usize_dec_eq(v_i_539_, v_stop_540_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; size_t v___x_545_; size_t v___x_546_; 
v___x_543_ = lean_array_uget_borrowed(v_as_538_, v_i_539_);
lean_inc(v___x_543_);
lean_inc(v___x_537_);
lean_inc(v_f_536_);
v___x_544_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go___redArg(v_f_536_, v___x_537_, v_b_541_, v___x_543_);
v___x_545_ = ((size_t)1ULL);
v___x_546_ = lean_usize_add(v_i_539_, v___x_545_);
v_i_539_ = v___x_546_;
v_b_541_ = v___x_544_;
goto _start;
}
else
{
lean_dec(v___x_537_);
lean_dec(v_f_536_);
return v_b_541_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_536_ = stack[0].m_obj;
lean_object* v___x_537_ = stack[1].m_obj;
lean_object* v_as_538_ = stack[2].m_obj;
size_t v_i_539_ = stack[3].m_num;
size_t v_stop_540_ = stack[4].m_num;
lean_object* v_b_541_ = stack[5].m_obj;
lean_object* v_res_548_;
v_res_548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_536_, v___x_537_, v_as_538_, v_i_539_, v_stop_540_, v_b_541_);
stack->m_obj
 = v_res_548_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg___boxed(lean_object* v_f_549_, lean_object* v___x_550_, lean_object* v_as_551_, lean_object* v_i_552_, lean_object* v_stop_553_, lean_object* v_b_554_){
_start:
{
size_t v_i_boxed_555_; size_t v_stop_boxed_556_; lean_object* v_res_557_; 
v_i_boxed_555_ = lean_unbox_usize(v_i_552_);
lean_dec(v_i_552_);
v_stop_boxed_556_ = lean_unbox_usize(v_stop_553_);
lean_dec(v_stop_553_);
v_res_557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_549_, v___x_550_, v_as_551_, v_i_boxed_555_, v_stop_boxed_556_, v_b_554_);
lean_dec_ref(v_as_551_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_558_, lean_object* v___x_559_, lean_object* v_as_560_, lean_object* v_i_561_, lean_object* v_stop_562_, lean_object* v_b_563_){
_start:
{
size_t v_i_boxed_564_; size_t v_stop_boxed_565_; lean_object* v_res_566_; 
v_i_boxed_564_ = lean_unbox_usize(v_i_561_);
lean_dec(v_i_561_);
v_stop_boxed_565_ = lean_unbox_usize(v_stop_562_);
lean_dec(v_stop_562_);
v_res_566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_558_, v___x_559_, v_as_560_, v_i_boxed_564_, v_stop_boxed_565_, v_b_563_);
lean_dec_ref(v_as_560_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg___boxed(lean_object* v_f_567_, lean_object* v___x_568_, lean_object* v_x_569_, lean_object* v_x_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(v_f_567_, v___x_568_, v_x_569_, v_x_570_);
lean_dec_ref(v_x_569_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___boxed(lean_object* v_f_572_, lean_object* v___x_573_, lean_object* v_x_574_, lean_object* v_x_575_, lean_object* v_x_576_, lean_object* v_x_577_){
_start:
{
size_t v_x_1172__boxed_578_; size_t v_x_1173__boxed_579_; lean_object* v_res_580_; 
v_x_1172__boxed_578_ = lean_unbox_usize(v_x_575_);
lean_dec(v_x_575_);
v_x_1173__boxed_579_ = lean_unbox_usize(v_x_576_);
lean_dec(v_x_576_);
v_res_580_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(v_f_572_, v___x_573_, v_x_574_, v_x_1172__boxed_578_, v_x_1173__boxed_579_, v_x_577_);
lean_dec_ref(v_x_574_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg___boxed(lean_object* v_f_581_, lean_object* v___x_582_, lean_object* v_t_583_, lean_object* v_init_584_, lean_object* v_start_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(v_f_581_, v___x_582_, v_t_583_, v_init_584_, v_start_585_);
lean_dec(v_start_585_);
lean_dec_ref(v_t_583_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go(lean_object* v_00_u03b1_587_, lean_object* v_f_588_, lean_object* v_ctx_x3f_589_, lean_object* v_a_590_, lean_object* v_x_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go___redArg(v_f_588_, v_ctx_x3f_589_, v_a_590_, v_x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0(lean_object* v_00_u03b1_593_, lean_object* v_f_594_, lean_object* v___x_595_, lean_object* v_t_596_, lean_object* v_init_597_, lean_object* v_start_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___redArg(v_f_594_, v___x_595_, v_t_596_, v_init_597_, v_start_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0___boxed(lean_object* v_00_u03b1_600_, lean_object* v_f_601_, lean_object* v___x_602_, lean_object* v_t_603_, lean_object* v_init_604_, lean_object* v_start_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0(v_00_u03b1_600_, v_f_601_, v___x_602_, v_t_603_, v_init_604_, v_start_605_);
lean_dec(v_start_605_);
lean_dec_ref(v_t_603_);
return v_res_606_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0(lean_object* v_00_u03b1_607_, lean_object* v_f_608_, lean_object* v___x_609_, lean_object* v_x_610_, size_t v_x_611_, size_t v_x_612_, lean_object* v_x_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg(v_f_608_, v___x_609_, v_x_610_, v_x_611_, v_x_612_, v_x_613_);
return v___x_614_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_608_ = stack[1].m_obj;
lean_object* v___x_609_ = stack[2].m_obj;
lean_object* v_x_610_ = stack[3].m_obj;
size_t v_x_611_ = stack[4].m_num;
size_t v_x_612_ = stack[5].m_num;
lean_object* v_x_613_ = stack[6].m_obj;
lean_object* v_res_615_;
v_res_615_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0(lean_box(0), v_f_608_, v___x_609_, v_x_610_, v_x_611_, v_x_612_, v_x_613_);
stack->m_obj
 = v_res_615_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_616_, lean_object* v_f_617_, lean_object* v___x_618_, lean_object* v_x_619_, lean_object* v_x_620_, lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
size_t v_x_1459__boxed_623_; size_t v_x_1460__boxed_624_; lean_object* v_res_625_; 
v_x_1459__boxed_623_ = lean_unbox_usize(v_x_620_);
lean_dec(v_x_620_);
v_x_1460__boxed_624_ = lean_unbox_usize(v_x_621_);
lean_dec(v_x_621_);
v_res_625_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0(v_00_u03b1_616_, v_f_617_, v___x_618_, v_x_619_, v_x_1459__boxed_623_, v_x_1460__boxed_624_, v_x_622_);
lean_dec_ref(v_x_619_);
return v_res_625_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1(lean_object* v_00_u03b1_626_, lean_object* v_f_627_, lean_object* v___x_628_, lean_object* v_as_629_, size_t v_i_630_, size_t v_stop_631_, lean_object* v_b_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___redArg(v_f_627_, v___x_628_, v_as_629_, v_i_630_, v_stop_631_, v_b_632_);
return v___x_633_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_627_ = stack[1].m_obj;
lean_object* v___x_628_ = stack[2].m_obj;
lean_object* v_as_629_ = stack[3].m_obj;
size_t v_i_630_ = stack[4].m_num;
size_t v_stop_631_ = stack[5].m_num;
lean_object* v_b_632_ = stack[6].m_obj;
lean_object* v_res_634_;
v_res_634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1(lean_box(0), v_f_627_, v___x_628_, v_as_629_, v_i_630_, v_stop_631_, v_b_632_);
stack->m_obj
 = v_res_634_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1___boxed(lean_object* v_00_u03b1_635_, lean_object* v_f_636_, lean_object* v___x_637_, lean_object* v_as_638_, lean_object* v_i_639_, lean_object* v_stop_640_, lean_object* v_b_641_){
_start:
{
size_t v_i_boxed_642_; size_t v_stop_boxed_643_; lean_object* v_res_644_; 
v_i_boxed_642_ = lean_unbox_usize(v_i_639_);
lean_dec(v_i_639_);
v_stop_boxed_643_ = lean_unbox_usize(v_stop_640_);
lean_dec(v_stop_640_);
v_res_644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__1(v_00_u03b1_635_, v_f_636_, v___x_637_, v_as_638_, v_i_boxed_642_, v_stop_boxed_643_, v_b_641_);
lean_dec_ref(v_as_638_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2(lean_object* v_00_u03b1_645_, lean_object* v_f_646_, lean_object* v___x_647_, lean_object* v_x_648_, lean_object* v_x_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___redArg(v_f_646_, v___x_647_, v_x_648_, v_x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2___boxed(lean_object* v_00_u03b1_651_, lean_object* v_f_652_, lean_object* v___x_653_, lean_object* v_x_654_, lean_object* v_x_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__2(v_00_u03b1_651_, v_f_652_, v___x_653_, v_x_654_, v_x_655_);
lean_dec_ref(v_x_654_);
return v_res_656_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_657_, lean_object* v_f_658_, lean_object* v___x_659_, lean_object* v_as_660_, size_t v_i_661_, size_t v_stop_662_, lean_object* v_b_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___redArg(v_f_658_, v___x_659_, v_as_660_, v_i_661_, v_stop_662_, v_b_663_);
return v___x_664_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_658_ = stack[1].m_obj;
lean_object* v___x_659_ = stack[2].m_obj;
lean_object* v_as_660_ = stack[3].m_obj;
size_t v_i_661_ = stack[4].m_num;
size_t v_stop_662_ = stack[5].m_num;
lean_object* v_b_663_ = stack[6].m_obj;
lean_object* v_res_665_;
v_res_665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1(lean_box(0), v_f_658_, v___x_659_, v_as_660_, v_i_661_, v_stop_662_, v_b_663_);
stack->m_obj
 = v_res_665_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_666_, lean_object* v_f_667_, lean_object* v___x_668_, lean_object* v_as_669_, lean_object* v_i_670_, lean_object* v_stop_671_, lean_object* v_b_672_){
_start:
{
size_t v_i_boxed_673_; size_t v_stop_boxed_674_; lean_object* v_res_675_; 
v_i_boxed_673_ = lean_unbox_usize(v_i_670_);
lean_dec(v_i_670_);
v_stop_boxed_674_ = lean_unbox_usize(v_stop_671_);
lean_dec(v_stop_671_);
v_res_675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0_spec__1(v_00_u03b1_666_, v_f_667_, v___x_668_, v_as_669_, v_i_boxed_673_, v_stop_boxed_674_, v_b_672_);
lean_dec_ref(v_as_669_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfo___redArg(lean_object* v_f_676_, lean_object* v_init_677_, lean_object* v_x_678_){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_box(0);
v___x_680_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go___redArg(v_f_676_, v___x_679_, v_init_677_, v_x_678_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfo(lean_object* v_00_u03b1_681_, lean_object* v_f_682_, lean_object* v_init_683_, lean_object* v_x_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v_f_682_, v_init_683_, v_x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__1(lean_object* v___f_686_, lean_object* v_a_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = lean_apply_1(v___f_686_, v_a_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0___boxed(lean_object* v_ctx_x3f_689_, lean_object* v_i_690_, lean_object* v_inst_691_, lean_object* v_f_692_, lean_object* v_children_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0(v_ctx_x3f_689_, v_i_690_, v_inst_691_, v_f_692_, v_children_693_, v_a_694_);
lean_dec_ref(v_i_690_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg(lean_object* v_inst_696_, lean_object* v_f_697_, lean_object* v_ctx_x3f_698_, lean_object* v_a_699_, lean_object* v_x_700_){
_start:
{
switch(lean_obj_tag(v_x_700_))
{
case 0:
{
lean_object* v_i_701_; lean_object* v_t_702_; lean_object* v___x_703_; 
v_i_701_ = lean_ctor_get(v_x_700_, 0);
lean_inc_ref(v_i_701_);
v_t_702_ = lean_ctor_get(v_x_700_, 1);
lean_inc_ref(v_t_702_);
lean_dec_ref_known(v_x_700_, 2);
v___x_703_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_701_, v_ctx_x3f_698_);
v_ctx_x3f_698_ = v___x_703_;
v_x_700_ = v_t_702_;
goto _start;
}
case 1:
{
lean_object* v_toApplicative_705_; lean_object* v_toBind_706_; lean_object* v_toPure_707_; lean_object* v_i_708_; lean_object* v_children_709_; lean_object* v___f_710_; 
v_toApplicative_705_ = lean_ctor_get(v_inst_696_, 0);
v_toBind_706_ = lean_ctor_get(v_inst_696_, 1);
lean_inc(v_toBind_706_);
v_toPure_707_ = lean_ctor_get(v_toApplicative_705_, 1);
lean_inc(v_toPure_707_);
v_i_708_ = lean_ctor_get(v_x_700_, 0);
lean_inc_ref_n(v_i_708_, 2);
v_children_709_ = lean_ctor_get(v_x_700_, 1);
lean_inc_ref(v_children_709_);
lean_dec_ref_known(v_x_700_, 2);
lean_inc(v_f_697_);
lean_inc(v_ctx_x3f_698_);
v___f_710_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_710_, 0, v_ctx_x3f_698_);
lean_closure_set(v___f_710_, 1, v_i_708_);
lean_closure_set(v___f_710_, 2, v_inst_696_);
lean_closure_set(v___f_710_, 3, v_f_697_);
lean_closure_set(v___f_710_, 4, v_children_709_);
if (lean_obj_tag(v_ctx_x3f_698_) == 0)
{
lean_object* v___f_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
lean_dec_ref(v_i_708_);
lean_dec(v_f_697_);
v___f_711_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__1), 2, 1);
lean_closure_set(v___f_711_, 0, v___f_710_);
v___x_712_ = lean_apply_2(v_toPure_707_, lean_box(0), v_a_699_);
v___x_713_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v___x_712_, v___f_711_);
return v___x_713_;
}
else
{
lean_object* v_val_714_; lean_object* v___f_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec(v_toPure_707_);
v_val_714_ = lean_ctor_get(v_ctx_x3f_698_, 0);
lean_inc(v_val_714_);
lean_dec_ref_known(v_ctx_x3f_698_, 1);
v___f_715_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__1), 2, 1);
lean_closure_set(v___f_715_, 0, v___f_710_);
v___x_716_ = lean_apply_3(v_f_697_, v_val_714_, v_i_708_, v_a_699_);
v___x_717_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v___x_716_, v___f_715_);
return v___x_717_;
}
}
default: 
{
lean_object* v_toApplicative_718_; lean_object* v_toPure_719_; lean_object* v___x_720_; 
v_toApplicative_718_ = lean_ctor_get(v_inst_696_, 0);
lean_inc_ref(v_toApplicative_718_);
lean_dec_ref_known(v_x_700_, 1);
lean_dec(v_ctx_x3f_698_);
lean_dec(v_f_697_);
lean_dec_ref(v_inst_696_);
v_toPure_719_ = lean_ctor_get(v_toApplicative_718_, 1);
lean_inc(v_toPure_719_);
lean_dec_ref(v_toApplicative_718_);
v___x_720_ = lean_apply_2(v_toPure_719_, lean_box(0), v_a_699_);
return v___x_720_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg___lam__0(lean_object* v_ctx_x3f_721_, lean_object* v_i_722_, lean_object* v_inst_723_, lean_object* v_f_724_, lean_object* v_children_725_, lean_object* v_a_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_727_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_721_, v_i_722_);
lean_inc_ref(v_inst_723_);
v___x_728_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg), 5, 3);
lean_closure_set(v___x_728_, 0, v_inst_723_);
lean_closure_set(v___x_728_, 1, v_f_724_);
lean_closure_set(v___x_728_, 2, v___x_727_);
v___x_729_ = lean_unsigned_to_nat(0u);
v___x_730_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_723_, v_children_725_, v___x_728_, v_a_726_, v___x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go(lean_object* v_m_731_, lean_object* v_00_u03b1_732_, lean_object* v_inst_733_, lean_object* v_f_734_, lean_object* v_ctx_x3f_735_, lean_object* v_a_736_, lean_object* v_x_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg(v_inst_733_, v_f_734_, v_ctx_x3f_735_, v_a_736_, v_x_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM___redArg(lean_object* v_inst_739_, lean_object* v_f_740_, lean_object* v_init_741_, lean_object* v_x_742_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_box(0);
v___x_744_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoM_go___redArg(v_inst_739_, v_f_740_, v___x_743_, v_init_741_, v_x_742_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoM(lean_object* v_m_745_, lean_object* v_00_u03b1_746_, lean_object* v_inst_747_, lean_object* v_f_748_, lean_object* v_init_749_, lean_object* v_x_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_Elab_InfoTree_foldInfoM___redArg(v_inst_747_, v_f_748_, v_init_749_, v_x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(lean_object* v_f_752_, lean_object* v___x_753_, lean_object* v_x_754_, lean_object* v_x_755_){
_start:
{
if (lean_obj_tag(v_x_754_) == 0)
{
lean_object* v_cs_756_; lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v_cs_756_ = lean_ctor_get(v_x_754_, 0);
v___x_757_ = lean_unsigned_to_nat(0u);
v___x_758_ = lean_array_get_size(v_cs_756_);
v___x_759_ = lean_nat_dec_lt(v___x_757_, v___x_758_);
if (v___x_759_ == 0)
{
lean_dec(v___x_753_);
lean_dec(v_f_752_);
return v_x_755_;
}
else
{
size_t v___x_760_; size_t v___x_761_; lean_object* v___x_762_; 
v___x_760_ = ((size_t)0ULL);
v___x_761_ = lean_usize_of_nat(v___x_758_);
v___x_762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_752_, v___x_753_, v_cs_756_, v___x_760_, v___x_761_, v_x_755_);
return v___x_762_;
}
}
else
{
lean_object* v_vs_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v_vs_763_ = lean_ctor_get(v_x_754_, 0);
v___x_764_ = lean_unsigned_to_nat(0u);
v___x_765_ = lean_array_get_size(v_vs_763_);
v___x_766_ = lean_nat_dec_lt(v___x_764_, v___x_765_);
if (v___x_766_ == 0)
{
lean_dec(v___x_753_);
lean_dec(v_f_752_);
return v_x_755_;
}
else
{
size_t v___x_767_; size_t v___x_768_; lean_object* v___x_769_; 
v___x_767_ = ((size_t)0ULL);
v___x_768_ = lean_usize_of_nat(v___x_765_);
v___x_769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_752_, v___x_753_, v_vs_763_, v___x_767_, v___x_768_, v_x_755_);
return v___x_769_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(lean_object* v_f_770_, lean_object* v___x_771_, lean_object* v_as_772_, size_t v_i_773_, size_t v_stop_774_, lean_object* v_b_775_){
_start:
{
uint8_t v___x_776_; 
v___x_776_ = lean_usize_dec_eq(v_i_773_, v_stop_774_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; size_t v___x_779_; size_t v___x_780_; 
v___x_777_ = lean_array_uget_borrowed(v_as_772_, v_i_773_);
lean_inc(v___x_771_);
lean_inc(v_f_770_);
v___x_778_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(v_f_770_, v___x_771_, v___x_777_, v_b_775_);
v___x_779_ = ((size_t)1ULL);
v___x_780_ = lean_usize_add(v_i_773_, v___x_779_);
v_i_773_ = v___x_780_;
v_b_775_ = v___x_778_;
goto _start;
}
else
{
lean_dec(v___x_771_);
lean_dec(v_f_770_);
return v_b_775_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_770_ = stack[0].m_obj;
lean_object* v___x_771_ = stack[1].m_obj;
lean_object* v_as_772_ = stack[2].m_obj;
size_t v_i_773_ = stack[3].m_num;
size_t v_stop_774_ = stack[4].m_num;
lean_object* v_b_775_ = stack[5].m_obj;
lean_object* v_res_782_;
v_res_782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_770_, v___x_771_, v_as_772_, v_i_773_, v_stop_774_, v_b_775_);
stack->m_obj
 = v_res_782_;
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(lean_object* v_f_783_, lean_object* v___x_784_, lean_object* v_x_785_, size_t v_x_786_, size_t v_x_787_, lean_object* v_x_788_){
_start:
{
if (lean_obj_tag(v_x_785_) == 0)
{
lean_object* v_cs_789_; lean_object* v___x_790_; size_t v___x_791_; lean_object* v_j_792_; lean_object* v___x_793_; size_t v___x_794_; size_t v___x_795_; size_t v___x_796_; size_t v___x_797_; size_t v___x_798_; size_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v_cs_789_ = lean_ctor_get(v_x_785_, 0);
v___x_790_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfo_go_spec__0_spec__0___redArg___closed__0);
v___x_791_ = lean_usize_shift_right(v_x_786_, v_x_787_);
v_j_792_ = lean_usize_to_nat(v___x_791_);
v___x_793_ = lean_array_get_borrowed(v___x_790_, v_cs_789_, v_j_792_);
v___x_794_ = ((size_t)1ULL);
v___x_795_ = lean_usize_shift_left(v___x_794_, v_x_787_);
v___x_796_ = lean_usize_sub(v___x_795_, v___x_794_);
v___x_797_ = lean_usize_land(v_x_786_, v___x_796_);
v___x_798_ = ((size_t)5ULL);
v___x_799_ = lean_usize_sub(v_x_787_, v___x_798_);
lean_inc(v___x_784_);
lean_inc(v_f_783_);
v___x_800_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(v_f_783_, v___x_784_, v___x_793_, v___x_797_, v___x_799_, v_x_788_);
v___x_801_ = lean_unsigned_to_nat(1u);
v___x_802_ = lean_nat_add(v_j_792_, v___x_801_);
lean_dec(v_j_792_);
v___x_803_ = lean_array_get_size(v_cs_789_);
v___x_804_ = lean_nat_dec_lt(v___x_802_, v___x_803_);
if (v___x_804_ == 0)
{
lean_dec(v___x_802_);
lean_dec(v___x_784_);
lean_dec(v_f_783_);
return v___x_800_;
}
else
{
size_t v___x_805_; size_t v___x_806_; lean_object* v___x_807_; 
v___x_805_ = lean_usize_of_nat(v___x_802_);
lean_dec(v___x_802_);
v___x_806_ = lean_usize_of_nat(v___x_803_);
v___x_807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_783_, v___x_784_, v_cs_789_, v___x_805_, v___x_806_, v___x_800_);
return v___x_807_;
}
}
else
{
lean_object* v_vs_808_; lean_object* v___x_809_; lean_object* v___x_810_; uint8_t v___x_811_; 
v_vs_808_ = lean_ctor_get(v_x_785_, 0);
v___x_809_ = lean_usize_to_nat(v_x_786_);
v___x_810_ = lean_array_get_size(v_vs_808_);
v___x_811_ = lean_nat_dec_lt(v___x_809_, v___x_810_);
if (v___x_811_ == 0)
{
lean_dec(v___x_809_);
lean_dec(v___x_784_);
lean_dec(v_f_783_);
return v_x_788_;
}
else
{
size_t v___x_812_; size_t v___x_813_; lean_object* v___x_814_; 
v___x_812_ = lean_usize_of_nat(v___x_809_);
lean_dec(v___x_809_);
v___x_813_ = lean_usize_of_nat(v___x_810_);
v___x_814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_783_, v___x_784_, v_vs_808_, v___x_812_, v___x_813_, v_x_788_);
return v___x_814_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_783_ = stack[0].m_obj;
lean_object* v___x_784_ = stack[1].m_obj;
lean_object* v_x_785_ = stack[2].m_obj;
size_t v_x_786_ = stack[3].m_num;
size_t v_x_787_ = stack[4].m_num;
lean_object* v_x_788_ = stack[5].m_obj;
lean_object* v_res_815_;
v_res_815_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(v_f_783_, v___x_784_, v_x_785_, v_x_786_, v_x_787_, v_x_788_);
stack->m_obj
 = v_res_815_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(lean_object* v_f_816_, lean_object* v___x_817_, lean_object* v_t_818_, lean_object* v_init_819_, lean_object* v_start_820_){
_start:
{
lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = lean_nat_dec_eq(v_start_820_, v___x_821_);
if (v___x_822_ == 0)
{
lean_object* v_root_823_; lean_object* v_tail_824_; size_t v_shift_825_; lean_object* v_tailOff_826_; uint8_t v___x_827_; 
v_root_823_ = lean_ctor_get(v_t_818_, 0);
v_tail_824_ = lean_ctor_get(v_t_818_, 1);
v_shift_825_ = lean_ctor_get_usize(v_t_818_, 4);
v_tailOff_826_ = lean_ctor_get(v_t_818_, 3);
v___x_827_ = lean_nat_dec_le(v_tailOff_826_, v_start_820_);
if (v___x_827_ == 0)
{
size_t v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_828_ = lean_usize_of_nat(v_start_820_);
lean_inc(v___x_817_);
lean_inc(v_f_816_);
v___x_829_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(v_f_816_, v___x_817_, v_root_823_, v___x_828_, v_shift_825_, v_init_819_);
v___x_830_ = lean_array_get_size(v_tail_824_);
v___x_831_ = lean_nat_dec_lt(v___x_821_, v___x_830_);
if (v___x_831_ == 0)
{
lean_dec(v___x_817_);
lean_dec(v_f_816_);
return v___x_829_;
}
else
{
size_t v___x_832_; size_t v___x_833_; lean_object* v___x_834_; 
v___x_832_ = ((size_t)0ULL);
v___x_833_ = lean_usize_of_nat(v___x_830_);
v___x_834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_816_, v___x_817_, v_tail_824_, v___x_832_, v___x_833_, v___x_829_);
return v___x_834_;
}
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_835_ = lean_nat_sub(v_start_820_, v_tailOff_826_);
v___x_836_ = lean_array_get_size(v_tail_824_);
v___x_837_ = lean_nat_dec_lt(v___x_835_, v___x_836_);
if (v___x_837_ == 0)
{
lean_dec(v___x_835_);
lean_dec(v___x_817_);
lean_dec(v_f_816_);
return v_init_819_;
}
else
{
size_t v___x_838_; size_t v___x_839_; lean_object* v___x_840_; 
v___x_838_ = lean_usize_of_nat(v___x_835_);
lean_dec(v___x_835_);
v___x_839_ = lean_usize_of_nat(v___x_836_);
v___x_840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_816_, v___x_817_, v_tail_824_, v___x_838_, v___x_839_, v_init_819_);
return v___x_840_;
}
}
}
else
{
lean_object* v_root_841_; lean_object* v_tail_842_; lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v_root_841_ = lean_ctor_get(v_t_818_, 0);
v_tail_842_ = lean_ctor_get(v_t_818_, 1);
lean_inc(v___x_817_);
lean_inc(v_f_816_);
v___x_843_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(v_f_816_, v___x_817_, v_root_841_, v_init_819_);
v___x_844_ = lean_array_get_size(v_tail_842_);
v___x_845_ = lean_nat_dec_lt(v___x_821_, v___x_844_);
if (v___x_845_ == 0)
{
lean_dec(v___x_817_);
lean_dec(v_f_816_);
return v___x_843_;
}
else
{
size_t v___x_846_; size_t v___x_847_; lean_object* v___x_848_; 
v___x_846_ = ((size_t)0ULL);
v___x_847_ = lean_usize_of_nat(v___x_844_);
v___x_848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_816_, v___x_817_, v_tail_842_, v___x_846_, v___x_847_, v___x_843_);
return v___x_848_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(lean_object* v_f_849_, lean_object* v_ctx_x3f_850_, lean_object* v_a_851_, lean_object* v_x_852_){
_start:
{
switch(lean_obj_tag(v_x_852_))
{
case 0:
{
lean_object* v_i_853_; lean_object* v_t_854_; lean_object* v___x_855_; 
v_i_853_ = lean_ctor_get(v_x_852_, 0);
lean_inc_ref(v_i_853_);
v_t_854_ = lean_ctor_get(v_x_852_, 1);
lean_inc_ref(v_t_854_);
lean_dec_ref_known(v_x_852_, 2);
v___x_855_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_853_, v_ctx_x3f_850_);
v_ctx_x3f_850_ = v___x_855_;
v_x_852_ = v_t_854_;
goto _start;
}
case 1:
{
lean_object* v_i_857_; lean_object* v_children_858_; lean_object* v___y_860_; 
v_i_857_ = lean_ctor_get(v_x_852_, 0);
lean_inc_ref(v_i_857_);
v_children_858_ = lean_ctor_get(v_x_852_, 1);
lean_inc_ref(v_children_858_);
if (lean_obj_tag(v_ctx_x3f_850_) == 0)
{
lean_dec_ref_known(v_x_852_, 2);
v___y_860_ = v_a_851_;
goto v___jp_859_;
}
else
{
lean_object* v_val_864_; lean_object* v___x_865_; 
v_val_864_ = lean_ctor_get(v_ctx_x3f_850_, 0);
lean_inc(v_f_849_);
lean_inc(v_val_864_);
v___x_865_ = lean_apply_3(v_f_849_, v_val_864_, v_x_852_, v_a_851_);
v___y_860_ = v___x_865_;
goto v___jp_859_;
}
v___jp_859_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_861_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_850_, v_i_857_);
lean_dec_ref(v_i_857_);
v___x_862_ = lean_unsigned_to_nat(0u);
v___x_863_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(v_f_849_, v___x_861_, v_children_858_, v___y_860_, v___x_862_);
lean_dec_ref(v_children_858_);
return v___x_863_;
}
}
default: 
{
lean_dec_ref_known(v_x_852_, 1);
lean_dec(v_ctx_x3f_850_);
lean_dec(v_f_849_);
return v_a_851_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(lean_object* v_f_866_, lean_object* v___x_867_, lean_object* v_as_868_, size_t v_i_869_, size_t v_stop_870_, lean_object* v_b_871_){
_start:
{
uint8_t v___x_872_; 
v___x_872_ = lean_usize_dec_eq(v_i_869_, v_stop_870_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; lean_object* v___x_874_; size_t v___x_875_; size_t v___x_876_; 
v___x_873_ = lean_array_uget_borrowed(v_as_868_, v_i_869_);
lean_inc(v___x_873_);
lean_inc(v___x_867_);
lean_inc(v_f_866_);
v___x_874_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(v_f_866_, v___x_867_, v_b_871_, v___x_873_);
v___x_875_ = ((size_t)1ULL);
v___x_876_ = lean_usize_add(v_i_869_, v___x_875_);
v_i_869_ = v___x_876_;
v_b_871_ = v___x_874_;
goto _start;
}
else
{
lean_dec(v___x_867_);
lean_dec(v_f_866_);
return v_b_871_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_866_ = stack[0].m_obj;
lean_object* v___x_867_ = stack[1].m_obj;
lean_object* v_as_868_ = stack[2].m_obj;
size_t v_i_869_ = stack[3].m_num;
size_t v_stop_870_ = stack[4].m_num;
lean_object* v_b_871_ = stack[5].m_obj;
lean_object* v_res_878_;
v_res_878_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_866_, v___x_867_, v_as_868_, v_i_869_, v_stop_870_, v_b_871_);
stack->m_obj
 = v_res_878_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg___boxed(lean_object* v_f_879_, lean_object* v___x_880_, lean_object* v_as_881_, lean_object* v_i_882_, lean_object* v_stop_883_, lean_object* v_b_884_){
_start:
{
size_t v_i_boxed_885_; size_t v_stop_boxed_886_; lean_object* v_res_887_; 
v_i_boxed_885_ = lean_unbox_usize(v_i_882_);
lean_dec(v_i_882_);
v_stop_boxed_886_ = lean_unbox_usize(v_stop_883_);
lean_dec(v_stop_883_);
v_res_887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_879_, v___x_880_, v_as_881_, v_i_boxed_885_, v_stop_boxed_886_, v_b_884_);
lean_dec_ref(v_as_881_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_888_, lean_object* v___x_889_, lean_object* v_as_890_, lean_object* v_i_891_, lean_object* v_stop_892_, lean_object* v_b_893_){
_start:
{
size_t v_i_boxed_894_; size_t v_stop_boxed_895_; lean_object* v_res_896_; 
v_i_boxed_894_ = lean_unbox_usize(v_i_891_);
lean_dec(v_i_891_);
v_stop_boxed_895_ = lean_unbox_usize(v_stop_892_);
lean_dec(v_stop_892_);
v_res_896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_888_, v___x_889_, v_as_890_, v_i_boxed_894_, v_stop_boxed_895_, v_b_893_);
lean_dec_ref(v_as_890_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg___boxed(lean_object* v_f_897_, lean_object* v___x_898_, lean_object* v_x_899_, lean_object* v_x_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(v_f_897_, v___x_898_, v_x_899_, v_x_900_);
lean_dec_ref(v_x_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg___boxed(lean_object* v_f_902_, lean_object* v___x_903_, lean_object* v_x_904_, lean_object* v_x_905_, lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
size_t v_x_1173__boxed_908_; size_t v_x_1174__boxed_909_; lean_object* v_res_910_; 
v_x_1173__boxed_908_ = lean_unbox_usize(v_x_905_);
lean_dec(v_x_905_);
v_x_1174__boxed_909_ = lean_unbox_usize(v_x_906_);
lean_dec(v_x_906_);
v_res_910_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(v_f_902_, v___x_903_, v_x_904_, v_x_1173__boxed_908_, v_x_1174__boxed_909_, v_x_907_);
lean_dec_ref(v_x_904_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg___boxed(lean_object* v_f_911_, lean_object* v___x_912_, lean_object* v_t_913_, lean_object* v_init_914_, lean_object* v_start_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(v_f_911_, v___x_912_, v_t_913_, v_init_914_, v_start_915_);
lean_dec(v_start_915_);
lean_dec_ref(v_t_913_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go(lean_object* v_00_u03b1_917_, lean_object* v_f_918_, lean_object* v_ctx_x3f_919_, lean_object* v_a_920_, lean_object* v_x_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(v_f_918_, v_ctx_x3f_919_, v_a_920_, v_x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0(lean_object* v_00_u03b1_923_, lean_object* v_f_924_, lean_object* v___x_925_, lean_object* v_t_926_, lean_object* v_init_927_, lean_object* v_start_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___redArg(v_f_924_, v___x_925_, v_t_926_, v_init_927_, v_start_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0___boxed(lean_object* v_00_u03b1_930_, lean_object* v_f_931_, lean_object* v___x_932_, lean_object* v_t_933_, lean_object* v_init_934_, lean_object* v_start_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0(v_00_u03b1_930_, v_f_931_, v___x_932_, v_t_933_, v_init_934_, v_start_935_);
lean_dec(v_start_935_);
lean_dec_ref(v_t_933_);
return v_res_936_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0(lean_object* v_00_u03b1_937_, lean_object* v_f_938_, lean_object* v___x_939_, lean_object* v_x_940_, size_t v_x_941_, size_t v_x_942_, lean_object* v_x_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___redArg(v_f_938_, v___x_939_, v_x_940_, v_x_941_, v_x_942_, v_x_943_);
return v___x_944_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_938_ = stack[1].m_obj;
lean_object* v___x_939_ = stack[2].m_obj;
lean_object* v_x_940_ = stack[3].m_obj;
size_t v_x_941_ = stack[4].m_num;
size_t v_x_942_ = stack[5].m_num;
lean_object* v_x_943_ = stack[6].m_obj;
lean_object* v_res_945_;
v_res_945_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0(lean_box(0), v_f_938_, v___x_939_, v_x_940_, v_x_941_, v_x_942_, v_x_943_);
stack->m_obj
 = v_res_945_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_946_, lean_object* v_f_947_, lean_object* v___x_948_, lean_object* v_x_949_, lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_x_952_){
_start:
{
size_t v_x_1458__boxed_953_; size_t v_x_1459__boxed_954_; lean_object* v_res_955_; 
v_x_1458__boxed_953_ = lean_unbox_usize(v_x_950_);
lean_dec(v_x_950_);
v_x_1459__boxed_954_ = lean_unbox_usize(v_x_951_);
lean_dec(v_x_951_);
v_res_955_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0(v_00_u03b1_946_, v_f_947_, v___x_948_, v_x_949_, v_x_1458__boxed_953_, v_x_1459__boxed_954_, v_x_952_);
lean_dec_ref(v_x_949_);
return v_res_955_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1(lean_object* v_00_u03b1_956_, lean_object* v_f_957_, lean_object* v___x_958_, lean_object* v_as_959_, size_t v_i_960_, size_t v_stop_961_, lean_object* v_b_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___redArg(v_f_957_, v___x_958_, v_as_959_, v_i_960_, v_stop_961_, v_b_962_);
return v___x_963_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_957_ = stack[1].m_obj;
lean_object* v___x_958_ = stack[2].m_obj;
lean_object* v_as_959_ = stack[3].m_obj;
size_t v_i_960_ = stack[4].m_num;
size_t v_stop_961_ = stack[5].m_num;
lean_object* v_b_962_ = stack[6].m_obj;
lean_object* v_res_964_;
v_res_964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1(lean_box(0), v_f_957_, v___x_958_, v_as_959_, v_i_960_, v_stop_961_, v_b_962_);
stack->m_obj
 = v_res_964_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1___boxed(lean_object* v_00_u03b1_965_, lean_object* v_f_966_, lean_object* v___x_967_, lean_object* v_as_968_, lean_object* v_i_969_, lean_object* v_stop_970_, lean_object* v_b_971_){
_start:
{
size_t v_i_boxed_972_; size_t v_stop_boxed_973_; lean_object* v_res_974_; 
v_i_boxed_972_ = lean_unbox_usize(v_i_969_);
lean_dec(v_i_969_);
v_stop_boxed_973_ = lean_unbox_usize(v_stop_970_);
lean_dec(v_stop_970_);
v_res_974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__1(v_00_u03b1_965_, v_f_966_, v___x_967_, v_as_968_, v_i_boxed_972_, v_stop_boxed_973_, v_b_971_);
lean_dec_ref(v_as_968_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2(lean_object* v_00_u03b1_975_, lean_object* v_f_976_, lean_object* v___x_977_, lean_object* v_x_978_, lean_object* v_x_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___redArg(v_f_976_, v___x_977_, v_x_978_, v_x_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2___boxed(lean_object* v_00_u03b1_981_, lean_object* v_f_982_, lean_object* v___x_983_, lean_object* v_x_984_, lean_object* v_x_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__2(v_00_u03b1_981_, v_f_982_, v___x_983_, v_x_984_, v_x_985_);
lean_dec_ref(v_x_984_);
return v_res_986_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_987_, lean_object* v_f_988_, lean_object* v___x_989_, lean_object* v_as_990_, size_t v_i_991_, size_t v_stop_992_, lean_object* v_b_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___redArg(v_f_988_, v___x_989_, v_as_990_, v_i_991_, v_stop_992_, v_b_993_);
return v___x_994_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_988_ = stack[1].m_obj;
lean_object* v___x_989_ = stack[2].m_obj;
lean_object* v_as_990_ = stack[3].m_obj;
size_t v_i_991_ = stack[4].m_num;
size_t v_stop_992_ = stack[5].m_num;
lean_object* v_b_993_ = stack[6].m_obj;
lean_object* v_res_995_;
v_res_995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1(lean_box(0), v_f_988_, v___x_989_, v_as_990_, v_i_991_, v_stop_992_, v_b_993_);
stack->m_obj
 = v_res_995_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_996_, lean_object* v_f_997_, lean_object* v___x_998_, lean_object* v_as_999_, lean_object* v_i_1000_, lean_object* v_stop_1001_, lean_object* v_b_1002_){
_start:
{
size_t v_i_boxed_1003_; size_t v_stop_boxed_1004_; lean_object* v_res_1005_; 
v_i_boxed_1003_ = lean_unbox_usize(v_i_1000_);
lean_dec(v_i_1000_);
v_stop_boxed_1004_ = lean_unbox_usize(v_stop_1001_);
lean_dec(v_stop_1001_);
v_res_1005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go_spec__0_spec__0_spec__1(v_00_u03b1_996_, v_f_997_, v___x_998_, v_as_999_, v_i_boxed_1003_, v_stop_boxed_1004_, v_b_1002_);
lean_dec_ref(v_as_999_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoTree___redArg(lean_object* v_init_1006_, lean_object* v_f_1007_, lean_object* v_x_1008_){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = lean_box(0);
v___x_1010_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_foldInfoTree_go___redArg(v_f_1007_, v___x_1009_, v_init_1006_, v_x_1008_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_foldInfoTree(lean_object* v_00_u03b1_1011_, lean_object* v_init_1012_, lean_object* v_f_1013_, lean_object* v_x_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_Elab_InfoTree_foldInfoTree___redArg(v_init_1012_, v_f_1013_, v_x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0(lean_object* v_toPure_1016_, lean_object* v_result_1017_, lean_object* v_____do__lift_1018_){
_start:
{
if (lean_obj_tag(v_____do__lift_1018_) == 0)
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_apply_2(v_toPure_1016_, lean_box(0), v_result_1017_);
return v___x_1019_;
}
else
{
lean_object* v_val_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_val_1020_ = lean_ctor_get(v_____do__lift_1018_, 0);
lean_inc(v_val_1020_);
v___x_1021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1021_, 0, v_val_1020_);
lean_ctor_set(v___x_1021_, 1, v_result_1017_);
v___x_1022_ = lean_apply_2(v_toPure_1016_, lean_box(0), v___x_1021_);
return v___x_1022_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0___boxed(lean_object* v_toPure_1023_, lean_object* v_result_1024_, lean_object* v_____do__lift_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0(v_toPure_1023_, v_result_1024_, v_____do__lift_1025_);
lean_dec(v_____do__lift_1025_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__1(lean_object* v_toPure_1027_, lean_object* v_f_1028_, lean_object* v_toBind_1029_, lean_object* v_ctx_1030_, lean_object* v_info_1031_, lean_object* v_result_1032_){
_start:
{
if (lean_obj_tag(v_info_1031_) == 1)
{
lean_object* v_i_1033_; lean_object* v___f_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v_i_1033_ = lean_ctor_get(v_info_1031_, 0);
lean_inc_ref(v_i_1033_);
lean_dec_ref_known(v_info_1031_, 1);
v___f_1034_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1034_, 0, v_toPure_1027_);
lean_closure_set(v___f_1034_, 1, v_result_1032_);
v___x_1035_ = lean_apply_2(v_f_1028_, v_ctx_1030_, v_i_1033_);
v___x_1036_ = lean_apply_4(v_toBind_1029_, lean_box(0), lean_box(0), v___x_1035_, v___f_1034_);
return v___x_1036_;
}
else
{
lean_object* v___x_1037_; 
lean_dec_ref(v_info_1031_);
lean_dec_ref(v_ctx_1030_);
lean_dec(v_toBind_1029_);
lean_dec(v_f_1028_);
v___x_1037_ = lean_apply_2(v_toPure_1027_, lean_box(0), v_result_1032_);
return v___x_1037_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM___redArg(lean_object* v_inst_1038_, lean_object* v_t_1039_, lean_object* v_f_1040_){
_start:
{
lean_object* v_toApplicative_1041_; lean_object* v_toBind_1042_; lean_object* v_toPure_1043_; lean_object* v___f_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v_toApplicative_1041_ = lean_ctor_get(v_inst_1038_, 0);
v_toBind_1042_ = lean_ctor_get(v_inst_1038_, 1);
v_toPure_1043_ = lean_ctor_get(v_toApplicative_1041_, 1);
lean_inc(v_toBind_1042_);
lean_inc(v_toPure_1043_);
v___f_1044_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectTermInfoM___redArg___lam__1), 6, 3);
lean_closure_set(v___f_1044_, 0, v_toPure_1043_);
lean_closure_set(v___f_1044_, 1, v_f_1040_);
lean_closure_set(v___f_1044_, 2, v_toBind_1042_);
v___x_1045_ = lean_box(0);
v___x_1046_ = l_Lean_Elab_InfoTree_foldInfoM___redArg(v_inst_1038_, v___f_1044_, v___x_1045_, v_t_1039_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_collectTermInfoM(lean_object* v_m_1047_, lean_object* v_00_u03b1_1048_, lean_object* v_inst_1049_, lean_object* v_t_1050_, lean_object* v_f_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_Elab_InfoTree_collectTermInfoM___redArg(v_inst_1049_, v_t_1050_, v_f_1051_);
return v___x_1052_;
}
}
uint8_t l_Lean_Elab_Info_isTerm(lean_object* v_x_1053_){
_start:
{
if (lean_obj_tag(v_x_1053_) == 1)
{
uint8_t v___x_1054_; 
v___x_1054_ = 1;
return v___x_1054_;
}
else
{
uint8_t v___x_1055_; 
v___x_1055_ = 0;
return v___x_1055_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Info_isTerm_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1053_ = stack[0].m_obj;
uint8_t v_res_1056_;
v_res_1056_ = l_Lean_Elab_Info_isTerm(v_x_1053_);
stack->m_num = v_res_1056_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_isTerm___boxed(lean_object* v_x_1057_){
_start:
{
uint8_t v_res_1058_; lean_object* v_r_1059_; 
v_res_1058_ = l_Lean_Elab_Info_isTerm(v_x_1057_);
lean_dec_ref(v_x_1057_);
v_r_1059_ = lean_box(v_res_1058_);
return v_r_1059_;
}
}
uint8_t l_Lean_Elab_Info_isCompletion(lean_object* v_x_1060_){
_start:
{
if (lean_obj_tag(v_x_1060_) == 8)
{
uint8_t v___x_1061_; 
v___x_1061_ = 1;
return v___x_1061_;
}
else
{
uint8_t v___x_1062_; 
v___x_1062_ = 0;
return v___x_1062_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Info_isCompletion_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1060_ = stack[0].m_obj;
uint8_t v_res_1063_;
v_res_1063_ = l_Lean_Elab_Info_isCompletion(v_x_1060_);
stack->m_num = v_res_1063_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_isCompletion___boxed(lean_object* v_x_1064_){
_start:
{
uint8_t v_res_1065_; lean_object* v_r_1066_; 
v_res_1065_ = l_Lean_Elab_Info_isCompletion(v_x_1064_);
lean_dec_ref(v_x_1064_);
v_r_1066_ = lean_box(v_res_1065_);
return v_r_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_getCompletionInfos___lam__0(lean_object* v_ctx_1067_, lean_object* v_info_1068_, lean_object* v_result_1069_){
_start:
{
if (lean_obj_tag(v_info_1068_) == 8)
{
lean_object* v_i_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v_i_1070_ = lean_ctor_get(v_info_1068_, 0);
lean_inc_ref(v_i_1070_);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v_ctx_1067_);
lean_ctor_set(v___x_1071_, 1, v_i_1070_);
v___x_1072_ = lean_array_push(v_result_1069_, v___x_1071_);
return v___x_1072_;
}
else
{
lean_dec_ref(v_ctx_1067_);
return v_result_1069_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_getCompletionInfos___lam__0___boxed(lean_object* v_ctx_1073_, lean_object* v_info_1074_, lean_object* v_result_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_Elab_InfoTree_getCompletionInfos___lam__0(v_ctx_1073_, v_info_1074_, v_result_1075_);
lean_dec_ref(v_info_1074_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_getCompletionInfos(lean_object* v_infoTree_1080_){
_start:
{
lean_object* v___f_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___f_1081_ = ((lean_object*)(l_Lean_Elab_InfoTree_getCompletionInfos___closed__0));
v___x_1082_ = ((lean_object*)(l_Lean_Elab_InfoTree_getCompletionInfos___closed__1));
v___x_1083_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_1081_, v___x_1082_, v_infoTree_1080_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_lctx(lean_object* v_x_1084_){
_start:
{
switch(lean_obj_tag(v_x_1084_))
{
case 1:
{
lean_object* v_i_1085_; lean_object* v_lctx_1086_; 
v_i_1085_ = lean_ctor_get(v_x_1084_, 0);
v_lctx_1086_ = lean_ctor_get(v_i_1085_, 1);
lean_inc_ref(v_lctx_1086_);
return v_lctx_1086_;
}
case 7:
{
lean_object* v_i_1087_; lean_object* v_lctx_1088_; 
v_i_1087_ = lean_ctor_get(v_x_1084_, 0);
v_lctx_1088_ = lean_ctor_get(v_i_1087_, 2);
lean_inc_ref(v_lctx_1088_);
return v_lctx_1088_;
}
case 13:
{
lean_object* v_i_1089_; lean_object* v_toTermInfo_1090_; lean_object* v_lctx_1091_; 
v_i_1089_ = lean_ctor_get(v_x_1084_, 0);
v_toTermInfo_1090_ = lean_ctor_get(v_i_1089_, 0);
v_lctx_1091_ = lean_ctor_get(v_toTermInfo_1090_, 1);
lean_inc_ref(v_lctx_1091_);
return v_lctx_1091_;
}
case 4:
{
lean_object* v_i_1092_; lean_object* v_lctx_1093_; 
v_i_1092_ = lean_ctor_get(v_x_1084_, 0);
v_lctx_1093_ = lean_ctor_get(v_i_1092_, 0);
lean_inc_ref(v_lctx_1093_);
return v_lctx_1093_;
}
case 8:
{
lean_object* v_i_1094_; lean_object* v___x_1095_; 
v_i_1094_ = lean_ctor_get(v_x_1084_, 0);
v___x_1095_ = l_Lean_Elab_CompletionInfo_lctx(v_i_1094_);
return v___x_1095_;
}
default: 
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_LocalContext_empty;
return v___x_1096_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_lctx___boxed(lean_object* v_x_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lean_Elab_Info_lctx(v_x_1097_);
lean_dec_ref(v_x_1097_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_pos_x3f(lean_object* v_i_1099_){
_start:
{
lean_object* v___x_1100_; uint8_t v___x_1101_; lean_object* v___x_1102_; 
v___x_1100_ = l_Lean_Elab_Info_stx(v_i_1099_);
v___x_1101_ = 1;
v___x_1102_ = l_Lean_Syntax_getPos_x3f(v___x_1100_, v___x_1101_);
lean_dec(v___x_1100_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_pos_x3f___boxed(lean_object* v_i_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_Elab_Info_pos_x3f(v_i_1103_);
lean_dec_ref(v_i_1103_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_tailPos_x3f(lean_object* v_i_1105_){
_start:
{
lean_object* v___x_1106_; uint8_t v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = l_Lean_Elab_Info_stx(v_i_1105_);
v___x_1107_ = 1;
v___x_1108_ = l_Lean_Syntax_getTailPos_x3f(v___x_1106_, v___x_1107_);
lean_dec(v___x_1106_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_tailPos_x3f___boxed(lean_object* v_i_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_Elab_Info_tailPos_x3f(v_i_1109_);
lean_dec_ref(v_i_1109_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_range_x3f(lean_object* v_i_1111_){
_start:
{
lean_object* v___x_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = l_Lean_Elab_Info_stx(v_i_1111_);
v___x_1113_ = 1;
v___x_1114_ = l_Lean_Syntax_getRange_x3f(v___x_1112_, v___x_1113_);
lean_dec(v___x_1112_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_range_x3f___boxed(lean_object* v_i_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_Elab_Info_range_x3f(v_i_1115_);
lean_dec_ref(v_i_1115_);
return v_res_1116_;
}
}
uint8_t l_Lean_Elab_Info_contains(lean_object* v_i_1117_, lean_object* v_pos_1118_, uint8_t v_includeStop_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_Lean_Elab_Info_range_x3f(v_i_1117_);
if (lean_obj_tag(v___x_1120_) == 0)
{
uint8_t v___x_1121_; 
v___x_1121_ = 0;
return v___x_1121_;
}
else
{
lean_object* v_val_1122_; uint8_t v___x_1123_; 
v_val_1122_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_val_1122_);
lean_dec_ref_known(v___x_1120_, 1);
v___x_1123_ = l_Lean_Syntax_Range_contains(v_val_1122_, v_pos_1118_, v_includeStop_1119_);
lean_dec(v_val_1122_);
return v___x_1123_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Info_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1117_ = stack[0].m_obj;
lean_object* v_pos_1118_ = stack[1].m_obj;
uint8_t v_includeStop_1119_ = stack[2].m_num;
uint8_t v_res_1124_;
v_res_1124_ = l_Lean_Elab_Info_contains(v_i_1117_, v_pos_1118_, v_includeStop_1119_);
stack->m_num = v_res_1124_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_contains___boxed(lean_object* v_i_1125_, lean_object* v_pos_1126_, lean_object* v_includeStop_1127_){
_start:
{
uint8_t v_includeStop_boxed_1128_; uint8_t v_res_1129_; lean_object* v_r_1130_; 
v_includeStop_boxed_1128_ = lean_unbox(v_includeStop_1127_);
v_res_1129_ = l_Lean_Elab_Info_contains(v_i_1125_, v_pos_1126_, v_includeStop_boxed_1128_);
lean_dec(v_pos_1126_);
lean_dec_ref(v_i_1125_);
v_r_1130_ = lean_box(v_res_1129_);
return v_r_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_size_x3f(lean_object* v_i_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_Elab_Info_pos_x3f(v_i_1131_);
if (lean_obj_tag(v___x_1132_) == 0)
{
return v___x_1132_;
}
else
{
lean_object* v_val_1133_; lean_object* v___x_1134_; 
v_val_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_val_1133_);
lean_dec_ref_known(v___x_1132_, 1);
v___x_1134_ = l_Lean_Elab_Info_tailPos_x3f(v_i_1131_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_dec(v_val_1133_);
return v___x_1134_;
}
else
{
lean_object* v_val_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1143_; 
v_val_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_val_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1139_ = lean_nat_sub(v_val_1135_, v_val_1133_);
lean_dec(v_val_1133_);
lean_dec(v_val_1135_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1139_);
v___x_1141_ = v___x_1137_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_size_x3f___boxed(lean_object* v_i_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_Elab_Info_size_x3f(v_i_1144_);
lean_dec_ref(v_i_1144_);
return v_res_1145_;
}
}
uint8_t l_Lean_Elab_Info_isSmaller(lean_object* v_i_u2081_1146_, lean_object* v_i_u2082_1147_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_Elab_Info_size_x3f(v_i_u2081_1146_);
if (lean_obj_tag(v___x_1148_) == 1)
{
lean_object* v_val_1149_; lean_object* v___x_1150_; 
v_val_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_val_1149_);
lean_dec_ref_known(v___x_1148_, 1);
v___x_1150_ = l_Lean_Elab_Info_size_x3f(v_i_u2082_1147_);
if (lean_obj_tag(v___x_1150_) == 0)
{
uint8_t v___x_1151_; 
lean_dec(v_val_1149_);
v___x_1151_ = 1;
return v___x_1151_;
}
else
{
lean_object* v_val_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; 
v_val_1152_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_val_1152_);
lean_dec_ref_known(v___x_1150_, 1);
v___x_1153_ = lean_unsigned_to_nat(1u);
v___x_1154_ = lean_nat_add(v_val_1149_, v___x_1153_);
lean_dec(v_val_1149_);
v___x_1155_ = lean_nat_dec_le(v___x_1154_, v_val_1152_);
lean_dec(v_val_1152_);
lean_dec(v___x_1154_);
return v___x_1155_;
}
}
else
{
uint8_t v___x_1156_; 
lean_dec(v___x_1148_);
v___x_1156_ = 0;
return v___x_1156_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Info_isSmaller_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_u2081_1146_ = stack[0].m_obj;
lean_object* v_i_u2082_1147_ = stack[1].m_obj;
uint8_t v_res_1157_;
v_res_1157_ = l_Lean_Elab_Info_isSmaller(v_i_u2081_1146_, v_i_u2082_1147_);
stack->m_num = v_res_1157_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_isSmaller___boxed(lean_object* v_i_u2081_1158_, lean_object* v_i_u2082_1159_){
_start:
{
uint8_t v_res_1160_; lean_object* v_r_1161_; 
v_res_1160_ = l_Lean_Elab_Info_isSmaller(v_i_u2081_1158_, v_i_u2082_1159_);
lean_dec_ref(v_i_u2082_1159_);
lean_dec_ref(v_i_u2081_1158_);
v_r_1161_ = lean_box(v_res_1160_);
return v_r_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_occursInside_x3f(lean_object* v_i_1162_, lean_object* v_hoverPos_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_Elab_Info_pos_x3f(v_i_1162_);
if (lean_obj_tag(v___x_1164_) == 0)
{
return v___x_1164_;
}
else
{
lean_object* v_val_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1182_; 
v_val_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1182_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_val_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1182_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
uint8_t v___y_1170_; lean_object* v___x_1176_; 
v___x_1176_ = l_Lean_Elab_Info_tailPos_x3f(v_i_1162_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_del_object(v___x_1167_);
lean_dec(v_val_1165_);
return v___x_1176_;
}
else
{
lean_object* v_val_1177_; uint8_t v___x_1178_; 
v_val_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_val_1177_);
lean_dec_ref_known(v___x_1176_, 1);
v___x_1178_ = lean_nat_dec_le(v_val_1165_, v_hoverPos_1163_);
if (v___x_1178_ == 0)
{
lean_dec(v_val_1177_);
v___y_1170_ = v___x_1178_;
goto v___jp_1169_;
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1179_ = lean_unsigned_to_nat(1u);
v___x_1180_ = lean_nat_add(v_hoverPos_1163_, v___x_1179_);
v___x_1181_ = lean_nat_dec_le(v___x_1180_, v_val_1177_);
lean_dec(v_val_1177_);
lean_dec(v___x_1180_);
v___y_1170_ = v___x_1181_;
goto v___jp_1169_;
}
}
v___jp_1169_:
{
if (v___y_1170_ == 0)
{
lean_object* v___x_1171_; 
lean_del_object(v___x_1167_);
lean_dec(v_val_1165_);
v___x_1171_ = lean_box(0);
return v___x_1171_;
}
else
{
lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1172_ = lean_nat_sub(v_hoverPos_1163_, v_val_1165_);
lean_dec(v_val_1165_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1172_);
v___x_1174_ = v___x_1167_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_occursInside_x3f___boxed(lean_object* v_i_1183_, lean_object* v_hoverPos_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_Elab_Info_occursInside_x3f(v_i_1183_, v_hoverPos_1184_);
lean_dec(v_hoverPos_1184_);
lean_dec_ref(v_i_1183_);
return v_res_1185_;
}
}
uint8_t l_Lean_Elab_Info_occursInOrOnBoundary(lean_object* v_i_1186_, lean_object* v_hoverPos_1187_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_Elab_Info_pos_x3f(v_i_1186_);
if (lean_obj_tag(v___x_1188_) == 1)
{
lean_object* v_val_1189_; lean_object* v___x_1190_; 
v_val_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_val_1189_);
lean_dec_ref_known(v___x_1188_, 1);
v___x_1190_ = l_Lean_Elab_Info_tailPos_x3f(v_i_1186_);
if (lean_obj_tag(v___x_1190_) == 1)
{
lean_object* v_val_1191_; uint8_t v___x_1192_; 
v_val_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_val_1191_);
lean_dec_ref_known(v___x_1190_, 1);
v___x_1192_ = lean_nat_dec_le(v_val_1189_, v_hoverPos_1187_);
lean_dec(v_val_1189_);
if (v___x_1192_ == 0)
{
lean_dec(v_val_1191_);
return v___x_1192_;
}
else
{
uint8_t v___x_1193_; 
v___x_1193_ = lean_nat_dec_le(v_hoverPos_1187_, v_val_1191_);
lean_dec(v_val_1191_);
return v___x_1193_;
}
}
else
{
uint8_t v___x_1194_; 
lean_dec(v___x_1190_);
lean_dec(v_val_1189_);
v___x_1194_ = 0;
return v___x_1194_;
}
}
else
{
uint8_t v___x_1195_; 
lean_dec(v___x_1188_);
v___x_1195_ = 0;
return v___x_1195_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Info_occursInOrOnBoundary_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1186_ = stack[0].m_obj;
lean_object* v_hoverPos_1187_ = stack[1].m_obj;
uint8_t v_res_1196_;
v_res_1196_ = l_Lean_Elab_Info_occursInOrOnBoundary(v_i_1186_, v_hoverPos_1187_);
stack->m_num = v_res_1196_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_occursInOrOnBoundary___boxed(lean_object* v_i_1197_, lean_object* v_hoverPos_1198_){
_start:
{
uint8_t v_res_1199_; lean_object* v_r_1200_; 
v_res_1199_ = l_Lean_Elab_Info_occursInOrOnBoundary(v_i_1197_, v_hoverPos_1198_);
lean_dec(v_hoverPos_1198_);
lean_dec_ref(v_i_1197_);
v_r_1200_ = lean_box(v_res_1199_);
return v_r_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0(lean_object* v_p_1201_, lean_object* v_ctx_1202_, lean_object* v_i_1203_, lean_object* v_x_1204_){
_start:
{
lean_object* v___x_1205_; uint8_t v___x_1206_; 
lean_inc_ref(v_i_1203_);
v___x_1205_ = lean_apply_1(v_p_1201_, v_i_1203_);
v___x_1206_ = lean_unbox(v___x_1205_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; 
lean_dec_ref(v_i_1203_);
lean_dec_ref(v_ctx_1202_);
v___x_1207_ = lean_box(0);
return v___x_1207_;
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v_ctx_1202_);
lean_ctor_set(v___x_1208_, 1, v_i_1203_);
v___x_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0___boxed(lean_object* v_p_1210_, lean_object* v_ctx_1211_, lean_object* v_i_1212_, lean_object* v_x_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0(v_p_1210_, v_ctx_1211_, v_i_1212_, v_x_1213_);
lean_dec_ref(v_x_1213_);
return v_res_1214_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(lean_object* v_as_1215_, size_t v_i_1216_, size_t v_stop_1217_, lean_object* v_b_1218_){
_start:
{
lean_object* v___y_1220_; uint8_t v___x_1224_; 
v___x_1224_ = lean_usize_dec_eq(v_i_1216_, v_stop_1217_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v_fst_1226_; lean_object* v_fst_1227_; uint8_t v___x_1228_; 
v___x_1225_ = lean_array_uget_borrowed(v_as_1215_, v_i_1216_);
v_fst_1226_ = lean_ctor_get(v___x_1225_, 0);
v_fst_1227_ = lean_ctor_get(v_b_1218_, 0);
v___x_1228_ = lean_nat_dec_lt(v_fst_1226_, v_fst_1227_);
if (v___x_1228_ == 0)
{
v___y_1220_ = v_b_1218_;
goto v___jp_1219_;
}
else
{
v___y_1220_ = v___x_1225_;
goto v___jp_1219_;
}
}
else
{
lean_inc_ref(v_b_1218_);
return v_b_1218_;
}
v___jp_1219_:
{
size_t v___x_1221_; size_t v___x_1222_; 
v___x_1221_ = ((size_t)1ULL);
v___x_1222_ = lean_usize_add(v_i_1216_, v___x_1221_);
v_i_1216_ = v___x_1222_;
v_b_1218_ = v___y_1220_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1215_ = stack[0].m_obj;
size_t v_i_1216_ = stack[1].m_num;
size_t v_stop_1217_ = stack[2].m_num;
lean_object* v_b_1218_ = stack[3].m_obj;
lean_object* v_res_1229_;
v_res_1229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(v_as_1215_, v_i_1216_, v_stop_1217_, v_b_1218_);
stack->m_obj
 = v_res_1229_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1___boxed(lean_object* v_as_1230_, lean_object* v_i_1231_, lean_object* v_stop_1232_, lean_object* v_b_1233_){
_start:
{
size_t v_i_boxed_1234_; size_t v_stop_boxed_1235_; lean_object* v_res_1236_; 
v_i_boxed_1234_ = lean_unbox_usize(v_i_1231_);
lean_dec(v_i_1231_);
v_stop_boxed_1235_ = lean_unbox_usize(v_stop_1232_);
lean_dec(v_stop_1232_);
v_res_1236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(v_as_1230_, v_i_boxed_1234_, v_stop_boxed_1235_, v_b_1233_);
lean_dec_ref(v_b_1233_);
lean_dec_ref(v_as_1230_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1(lean_object* v_as_1237_){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; 
v___x_1238_ = lean_unsigned_to_nat(0u);
v___x_1239_ = lean_array_get_size(v_as_1237_);
v___x_1240_ = lean_nat_dec_lt(v___x_1238_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_box(0);
return v___x_1241_;
}
else
{
lean_object* v_a0_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v_a0_1242_ = lean_array_fget_borrowed(v_as_1237_, v___x_1238_);
v___x_1243_ = lean_unsigned_to_nat(1u);
v___x_1244_ = lean_nat_dec_lt(v___x_1243_, v___x_1239_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; 
lean_inc(v_a0_1242_);
v___x_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1245_, 0, v_a0_1242_);
return v___x_1245_;
}
else
{
size_t v___x_1246_; size_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1246_ = ((size_t)1ULL);
v___x_1247_ = lean_usize_of_nat(v___x_1239_);
v___x_1248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1_spec__1(v_as_1237_, v___x_1246_, v___x_1247_, v_a0_1242_);
v___x_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
return v___x_1249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1___boxed(lean_object* v_as_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1(v_as_1250_);
lean_dec_ref(v_as_1250_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__0(lean_object* v_a_1252_, lean_object* v_a_1253_){
_start:
{
if (lean_obj_tag(v_a_1252_) == 0)
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_array_to_list(v_a_1253_);
return v___x_1254_;
}
else
{
lean_object* v_head_1255_; lean_object* v_tail_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1273_; 
v_head_1255_ = lean_ctor_get(v_a_1252_, 0);
v_tail_1256_ = lean_ctor_get(v_a_1252_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_a_1252_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1258_ = v_a_1252_;
v_isShared_1259_ = v_isSharedCheck_1273_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_tail_1256_);
lean_inc(v_head_1255_);
lean_dec(v_a_1252_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1273_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v_snd_1260_; lean_object* v___x_1261_; 
v_snd_1260_ = lean_ctor_get(v_head_1255_, 1);
v___x_1261_ = l_Lean_Elab_Info_pos_x3f(v_snd_1260_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_del_object(v___x_1258_);
lean_dec(v_head_1255_);
v_a_1252_ = v_tail_1256_;
goto _start;
}
else
{
lean_object* v_val_1263_; lean_object* v___x_1264_; 
v_val_1263_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_val_1263_);
lean_dec_ref_known(v___x_1261_, 1);
v___x_1264_ = l_Lean_Elab_Info_tailPos_x3f(v_snd_1260_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_dec(v_val_1263_);
lean_del_object(v___x_1258_);
lean_dec(v_head_1255_);
v_a_1252_ = v_tail_1256_;
goto _start;
}
else
{
lean_object* v_val_1266_; lean_object* v___x_1267_; lean_object* v___x_1269_; 
v_val_1266_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_val_1266_);
lean_dec_ref_known(v___x_1264_, 1);
v___x_1267_ = lean_nat_sub(v_val_1266_, v_val_1263_);
lean_dec(v_val_1263_);
lean_dec(v_val_1266_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set_tag(v___x_1258_, 0);
lean_ctor_set(v___x_1258_, 1, v_head_1255_);
lean_ctor_set(v___x_1258_, 0, v___x_1267_);
v___x_1269_ = v___x_1258_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1267_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_head_1255_);
v___x_1269_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1270_; 
v___x_1270_ = lean_array_push(v_a_1253_, v___x_1269_);
v_a_1252_ = v_tail_1256_;
v_a_1253_ = v___x_1270_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f(lean_object* v_p_1276_, lean_object* v_t_1277_){
_start:
{
lean_object* v___f_1278_; lean_object* v_ts_1279_; lean_object* v___x_1280_; lean_object* v_infos_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___f_1278_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_smallestInfo_x3f___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1278_, 0, v_p_1276_);
v_ts_1279_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_1278_, v_t_1277_);
v___x_1280_ = ((lean_object*)(l_Lean_Elab_InfoTree_smallestInfo_x3f___closed__0));
v_infos_1281_ = l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__0(v_ts_1279_, v___x_1280_);
v___x_1282_ = lean_array_mk(v_infos_1281_);
v___x_1283_ = l_Array_getMax_x3f___at___00Lean_Elab_InfoTree_smallestInfo_x3f_spec__1(v___x_1282_);
lean_dec_ref(v___x_1282_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_box(0);
return v___x_1284_;
}
else
{
lean_object* v_val_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1293_; 
v_val_1285_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1287_ = v___x_1283_;
v_isShared_1288_ = v_isSharedCheck_1293_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_val_1285_);
lean_dec(v___x_1283_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1293_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v_snd_1289_; lean_object* v___x_1291_; 
v_snd_1289_ = lean_ctor_get(v_val_1285_, 1);
lean_inc(v_snd_1289_);
lean_dec(v_val_1285_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v_snd_1289_);
v___x_1291_ = v___x_1287_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_snd_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
uint8_t l_Lean_Elab_instBEqHoverableInfoPrio_beq(lean_object* v_x_1294_, lean_object* v_x_1295_){
_start:
{
uint8_t v_isHoverPosOnStop_1296_; lean_object* v_size_1297_; uint8_t v_isVariableInfo_1298_; uint8_t v_isPartialTermInfo_1299_; uint8_t v_isHoverPosOnStop_1300_; lean_object* v_size_1301_; uint8_t v_isVariableInfo_1302_; uint8_t v_isPartialTermInfo_1303_; uint8_t v___y_1305_; 
v_isHoverPosOnStop_1296_ = lean_ctor_get_uint8(v_x_1294_, sizeof(void*)*1);
v_size_1297_ = lean_ctor_get(v_x_1294_, 0);
v_isVariableInfo_1298_ = lean_ctor_get_uint8(v_x_1294_, sizeof(void*)*1 + 1);
v_isPartialTermInfo_1299_ = lean_ctor_get_uint8(v_x_1294_, sizeof(void*)*1 + 2);
v_isHoverPosOnStop_1300_ = lean_ctor_get_uint8(v_x_1295_, sizeof(void*)*1);
v_size_1301_ = lean_ctor_get(v_x_1295_, 0);
v_isVariableInfo_1302_ = lean_ctor_get_uint8(v_x_1295_, sizeof(void*)*1 + 1);
v_isPartialTermInfo_1303_ = lean_ctor_get_uint8(v_x_1295_, sizeof(void*)*1 + 2);
if (v_isHoverPosOnStop_1300_ == 0)
{
if (v_isHoverPosOnStop_1296_ == 0)
{
goto v___jp_1306_;
}
else
{
return v_isHoverPosOnStop_1300_;
}
}
else
{
if (v_isHoverPosOnStop_1296_ == 0)
{
return v_isHoverPosOnStop_1296_;
}
else
{
goto v___jp_1306_;
}
}
v___jp_1304_:
{
if (v___y_1305_ == 0)
{
return v___y_1305_;
}
else
{
if (v_isPartialTermInfo_1303_ == 0)
{
if (v_isPartialTermInfo_1299_ == 0)
{
return v___y_1305_;
}
else
{
return v_isPartialTermInfo_1303_;
}
}
else
{
return v_isPartialTermInfo_1299_;
}
}
}
v___jp_1306_:
{
uint8_t v___x_1307_; 
v___x_1307_ = lean_nat_dec_eq(v_size_1297_, v_size_1301_);
if (v___x_1307_ == 0)
{
return v___x_1307_;
}
else
{
if (v_isVariableInfo_1302_ == 0)
{
if (v_isVariableInfo_1298_ == 0)
{
v___y_1305_ = v___x_1307_;
goto v___jp_1304_;
}
else
{
return v_isVariableInfo_1302_;
}
}
else
{
v___y_1305_ = v_isVariableInfo_1298_;
goto v___jp_1304_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_instBEqHoverableInfoPrio_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1294_ = stack[0].m_obj;
lean_object* v_x_1295_ = stack[1].m_obj;
uint8_t v_res_1308_;
v_res_1308_ = l_Lean_Elab_instBEqHoverableInfoPrio_beq(v_x_1294_, v_x_1295_);
stack->m_num = v_res_1308_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_instBEqHoverableInfoPrio_beq___boxed(lean_object* v_x_1309_, lean_object* v_x_1310_){
_start:
{
uint8_t v_res_1311_; lean_object* v_r_1312_; 
v_res_1311_ = l_Lean_Elab_instBEqHoverableInfoPrio_beq(v_x_1309_, v_x_1310_);
lean_dec_ref(v_x_1310_);
lean_dec_ref(v_x_1309_);
v_r_1312_ = lean_box(v_res_1311_);
return v_r_1312_;
}
}
uint8_t l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(lean_object* v_i1_1315_, lean_object* v_i2_1316_){
_start:
{
uint8_t v_isHoverPosOnStop_1317_; lean_object* v_size_1318_; uint8_t v_isVariableInfo_1319_; uint8_t v_isPartialTermInfo_1320_; uint8_t v___y_1322_; uint8_t v___y_1345_; 
v_isHoverPosOnStop_1317_ = lean_ctor_get_uint8(v_i1_1315_, sizeof(void*)*1);
v_size_1318_ = lean_ctor_get(v_i1_1315_, 0);
v_isVariableInfo_1319_ = lean_ctor_get_uint8(v_i1_1315_, sizeof(void*)*1 + 1);
v_isPartialTermInfo_1320_ = lean_ctor_get_uint8(v_i1_1315_, sizeof(void*)*1 + 2);
if (v_isHoverPosOnStop_1317_ == 0)
{
v___y_1345_ = v_isHoverPosOnStop_1317_;
goto v___jp_1344_;
}
else
{
uint8_t v_isHoverPosOnStop_1346_; 
v_isHoverPosOnStop_1346_ = lean_ctor_get_uint8(v_i2_1316_, sizeof(void*)*1);
if (v_isHoverPosOnStop_1346_ == 0)
{
uint8_t v___x_1347_; 
v___x_1347_ = 0;
return v___x_1347_;
}
else
{
uint8_t v___x_1348_; 
v___x_1348_ = 0;
v___y_1345_ = v___x_1348_;
goto v___jp_1344_;
}
}
v___jp_1321_:
{
if (v_isPartialTermInfo_1320_ == 0)
{
uint8_t v_isPartialTermInfo_1323_; 
v_isPartialTermInfo_1323_ = lean_ctor_get_uint8(v_i2_1316_, sizeof(void*)*1 + 2);
if (v_isPartialTermInfo_1323_ == 0)
{
uint8_t v___x_1324_; 
v___x_1324_ = 1;
return v___x_1324_;
}
else
{
uint8_t v___x_1325_; 
v___x_1325_ = 2;
return v___x_1325_;
}
}
else
{
uint8_t v_isPartialTermInfo_1326_; 
v_isPartialTermInfo_1326_ = lean_ctor_get_uint8(v_i2_1316_, sizeof(void*)*1 + 2);
if (v_isPartialTermInfo_1326_ == 0)
{
uint8_t v___x_1327_; 
v___x_1327_ = 0;
return v___x_1327_;
}
else
{
if (v___y_1322_ == 0)
{
uint8_t v___x_1328_; 
v___x_1328_ = 1;
return v___x_1328_;
}
else
{
uint8_t v___x_1329_; 
v___x_1329_ = 0;
return v___x_1329_;
}
}
}
}
v___jp_1330_:
{
uint8_t v_isVariableInfo_1331_; 
v_isVariableInfo_1331_ = lean_ctor_get_uint8(v_i2_1316_, sizeof(void*)*1 + 1);
if (v_isVariableInfo_1331_ == 0)
{
v___y_1322_ = v_isVariableInfo_1331_;
goto v___jp_1321_;
}
else
{
uint8_t v___x_1332_; 
v___x_1332_ = 2;
return v___x_1332_;
}
}
v___jp_1333_:
{
lean_object* v_size_1334_; uint8_t v_isVariableInfo_1335_; uint8_t v___x_1336_; 
v_size_1334_ = lean_ctor_get(v_i2_1316_, 0);
v_isVariableInfo_1335_ = lean_ctor_get_uint8(v_i2_1316_, sizeof(void*)*1 + 1);
v___x_1336_ = lean_nat_dec_lt(v_size_1334_, v_size_1318_);
if (v___x_1336_ == 0)
{
uint8_t v___x_1337_; 
v___x_1337_ = lean_nat_dec_lt(v_size_1318_, v_size_1334_);
if (v___x_1337_ == 0)
{
if (v_isVariableInfo_1319_ == 0)
{
goto v___jp_1330_;
}
else
{
if (v_isVariableInfo_1335_ == 0)
{
uint8_t v___x_1338_; 
v___x_1338_ = 0;
return v___x_1338_;
}
else
{
if (v___x_1337_ == 0)
{
v___y_1322_ = v___x_1337_;
goto v___jp_1321_;
}
else
{
goto v___jp_1330_;
}
}
}
}
else
{
uint8_t v___x_1339_; 
v___x_1339_ = 2;
return v___x_1339_;
}
}
else
{
uint8_t v___x_1340_; 
v___x_1340_ = 0;
return v___x_1340_;
}
}
v___jp_1341_:
{
uint8_t v_isHoverPosOnStop_1342_; 
v_isHoverPosOnStop_1342_ = lean_ctor_get_uint8(v_i2_1316_, sizeof(void*)*1);
if (v_isHoverPosOnStop_1342_ == 0)
{
goto v___jp_1333_;
}
else
{
uint8_t v___x_1343_; 
v___x_1343_ = 2;
return v___x_1343_;
}
}
v___jp_1344_:
{
if (v_isHoverPosOnStop_1317_ == 0)
{
goto v___jp_1341_;
}
else
{
if (v___y_1345_ == 0)
{
goto v___jp_1333_;
}
else
{
goto v___jp_1341_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_instOrdHoverableInfoPrio___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_i1_1315_ = stack[0].m_obj;
lean_object* v_i2_1316_ = stack[1].m_obj;
uint8_t v_res_1349_;
v_res_1349_ = l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(v_i1_1315_, v_i2_1316_);
stack->m_num = v_res_1349_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_instOrdHoverableInfoPrio___lam__0___boxed(lean_object* v_i1_1350_, lean_object* v_i2_1351_){
_start:
{
uint8_t v_res_1352_; lean_object* v_r_1353_; 
v_res_1352_ = l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(v_i1_1350_, v_i2_1351_);
lean_dec_ref(v_i2_1351_);
lean_dec_ref(v_i1_1350_);
v_r_1353_ = lean_box(v_res_1352_);
return v_r_1353_;
}
}
static lean_object* _init_l_Lean_Elab_instLEHoverableInfoPrio(void){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_box(0);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMaxHoverableInfoPrio___lam__0(lean_object* v_x_1357_, lean_object* v_y_1358_){
_start:
{
uint8_t v___x_1359_; 
v___x_1359_ = l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(v_x_1357_, v_y_1358_);
if (v___x_1359_ == 2)
{
lean_inc_ref(v_x_1357_);
return v_x_1357_;
}
else
{
lean_inc_ref(v_y_1358_);
return v_y_1358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMaxHoverableInfoPrio___lam__0___boxed(lean_object* v_x_1360_, lean_object* v_y_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_Elab_instMaxHoverableInfoPrio___lam__0(v_x_1360_, v_y_1361_);
lean_dec_ref(v_y_1361_);
lean_dec_ref(v_x_1360_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0(lean_object* v_x_1365_){
_start:
{
lean_object* v_fst_1366_; 
v_fst_1366_ = lean_ctor_get(v_x_1365_, 0);
lean_inc(v_fst_1366_);
return v_fst_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0___boxed(lean_object* v_x_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__0(v_x_1367_);
lean_dec_ref(v_x_1367_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1(lean_object* v_r_x3f_1369_){
_start:
{
if (lean_obj_tag(v_r_x3f_1369_) == 0)
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_box(0);
return v___x_1370_;
}
else
{
lean_object* v_val_1371_; 
v_val_1371_ = lean_ctor_get(v_r_x3f_1369_, 0);
lean_inc(v_val_1371_);
return v_val_1371_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1___boxed(lean_object* v_r_x3f_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__1(v_r_x3f_1372_);
lean_dec(v_r_x3f_1372_);
return v_res_1373_;
}
}
uint8_t l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2(lean_object* v___x_1374_, lean_object* v_maxPrio_x3f_1375_, lean_object* v_x_1376_){
_start:
{
lean_object* v_fst_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v_fst_1377_ = lean_ctor_get(v_x_1376_, 0);
lean_inc(v_fst_1377_);
v___x_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1378_, 0, v_fst_1377_);
v___x_1379_ = l_instBEqOption_beq___redArg(v___x_1374_, v___x_1378_, v_maxPrio_x3f_1375_);
return v___x_1379_;
}
}
LEAN_EXPORT void l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1374_ = stack[0].m_obj;
lean_object* v_maxPrio_x3f_1375_ = stack[1].m_obj;
lean_object* v_x_1376_ = stack[2].m_obj;
uint8_t v_res_1380_;
v_res_1380_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2(v___x_1374_, v_maxPrio_x3f_1375_, v_x_1376_);
stack->m_num = v_res_1380_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2___boxed(lean_object* v___x_1381_, lean_object* v_maxPrio_x3f_1382_, lean_object* v_x_1383_){
_start:
{
uint8_t v_res_1384_; lean_object* v_r_1385_; 
v_res_1384_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2(v___x_1381_, v_maxPrio_x3f_1382_, v_x_1383_);
lean_dec_ref(v_x_1383_);
v_r_1385_ = lean_box(v_res_1384_);
return v_r_1385_;
}
}
lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3(lean_object* v___f_1398_, lean_object* v___f_1399_, lean_object* v___x_1400_, lean_object* v_toPure_1401_, lean_object* v_ctx_1402_, lean_object* v_info_1403_, lean_object* v_children_1404_, lean_object* v_hoverPos_1405_, uint8_t v_includeStop_1406_, lean_object* v_results_1407_){
_start:
{
uint8_t v___y_1409_; uint8_t v___y_1410_; lean_object* v___y_1411_; uint8_t v___y_1412_; uint8_t v___y_1419_; uint8_t v___y_1420_; uint8_t v___y_1421_; lean_object* v___y_1422_; uint8_t v___y_1423_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v_maxPrio_x3f_1429_; lean_object* v___f_1430_; lean_object* v_bestResult_x3f_1431_; 
v___x_1427_ = lean_box(0);
lean_inc(v_results_1407_);
v___x_1428_ = l_List_mapTR_loop___redArg(v___f_1398_, v_results_1407_, v___x_1427_);
v_maxPrio_x3f_1429_ = l_List_max_x3f___redArg(v___f_1399_, v___x_1428_);
v___f_1430_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_1430_, 0, v___x_1400_);
lean_closure_set(v___f_1430_, 1, v_maxPrio_x3f_1429_);
v_bestResult_x3f_1431_ = l_List_find_x3f___redArg(v___f_1430_, v_results_1407_);
if (lean_obj_tag(v_bestResult_x3f_1431_) == 1)
{
lean_object* v___x_1432_; 
lean_dec_ref(v_children_1404_);
lean_dec_ref(v_info_1403_);
lean_dec_ref(v_ctx_1402_);
v___x_1432_ = lean_apply_2(v_toPure_1401_, lean_box(0), v_bestResult_x3f_1431_);
return v___x_1432_;
}
else
{
lean_object* v___x_1433_; uint8_t v___y_1435_; uint8_t v___y_1436_; uint8_t v___y_1437_; uint8_t v___y_1450_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
lean_dec(v_bestResult_x3f_1431_);
v___x_1433_ = l_Lean_Elab_Info_stx(v_info_1403_);
v___x_1455_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__1));
lean_inc(v___x_1433_);
v___x_1456_ = l_Lean_Syntax_isOfKind(v___x_1433_, v___x_1455_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; 
lean_inc_ref(v_info_1403_);
v___x_1457_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_1403_);
if (lean_obj_tag(v___x_1457_) == 0)
{
v___y_1450_ = v___x_1456_;
goto v___jp_1449_;
}
else
{
lean_object* v_val_1458_; lean_object* v_elaborator_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v_val_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_val_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v_elaborator_1459_ = lean_ctor_get(v_val_1458_, 0);
lean_inc(v_elaborator_1459_);
lean_dec(v_val_1458_);
v___x_1460_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6));
v___x_1461_ = lean_name_eq(v_elaborator_1459_, v___x_1460_);
lean_dec(v_elaborator_1459_);
v___y_1450_ = v___x_1461_;
goto v___jp_1449_;
}
}
else
{
v___y_1450_ = v___x_1456_;
goto v___jp_1449_;
}
v___jp_1434_:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_Syntax_getRange_x3f(v___x_1433_, v___y_1436_);
lean_dec(v___x_1433_);
if (lean_obj_tag(v___x_1438_) == 1)
{
lean_object* v_val_1439_; uint8_t v___x_1440_; 
v_val_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_val_1439_);
lean_dec_ref_known(v___x_1438_, 1);
v___x_1440_ = l_Lean_Syntax_Range_contains(v_val_1439_, v_hoverPos_1405_, v_includeStop_1406_);
if (v___x_1440_ == 0)
{
lean_dec(v_val_1439_);
lean_dec_ref(v_children_1404_);
lean_dec_ref(v_info_1403_);
lean_dec_ref(v_ctx_1402_);
goto v___jp_1424_;
}
else
{
if (v___y_1437_ == 0)
{
lean_dec(v_val_1439_);
lean_dec_ref(v_children_1404_);
lean_dec_ref(v_info_1403_);
lean_dec_ref(v_ctx_1402_);
goto v___jp_1424_;
}
else
{
lean_object* v_start_1441_; lean_object* v_stop_1442_; uint8_t v_decide_1443_; lean_object* v___x_1444_; 
v_start_1441_ = lean_ctor_get(v_val_1439_, 0);
lean_inc(v_start_1441_);
v_stop_1442_ = lean_ctor_get(v_val_1439_, 1);
lean_inc(v_stop_1442_);
lean_dec(v_val_1439_);
v_decide_1443_ = lean_nat_dec_eq(v_stop_1442_, v_hoverPos_1405_);
v___x_1444_ = lean_nat_sub(v_stop_1442_, v_start_1441_);
lean_dec(v_start_1441_);
lean_dec(v_stop_1442_);
if (lean_obj_tag(v_info_1403_) == 1)
{
lean_object* v_i_1445_; lean_object* v_expr_1446_; 
v_i_1445_ = lean_ctor_get(v_info_1403_, 0);
v_expr_1446_ = lean_ctor_get(v_i_1445_, 3);
if (lean_obj_tag(v_expr_1446_) == 1)
{
v___y_1419_ = v_decide_1443_;
v___y_1420_ = v___y_1435_;
v___y_1421_ = v___y_1436_;
v___y_1422_ = v___x_1444_;
v___y_1423_ = v___y_1436_;
goto v___jp_1418_;
}
else
{
v___y_1419_ = v_decide_1443_;
v___y_1420_ = v___y_1435_;
v___y_1421_ = v___y_1436_;
v___y_1422_ = v___x_1444_;
v___y_1423_ = v___y_1435_;
goto v___jp_1418_;
}
}
else
{
v___y_1419_ = v_decide_1443_;
v___y_1420_ = v___y_1435_;
v___y_1421_ = v___y_1436_;
v___y_1422_ = v___x_1444_;
v___y_1423_ = v___y_1435_;
goto v___jp_1418_;
}
}
}
}
else
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec(v___x_1438_);
lean_dec_ref(v_children_1404_);
lean_dec_ref(v_info_1403_);
lean_dec_ref(v_ctx_1402_);
v___x_1447_ = lean_box(0);
v___x_1448_ = lean_apply_2(v_toPure_1401_, lean_box(0), v___x_1447_);
return v___x_1448_;
}
}
v___jp_1449_:
{
if (v___y_1450_ == 0)
{
uint8_t v___x_1451_; 
v___x_1451_ = 1;
switch(lean_obj_tag(v_info_1403_))
{
case 7:
{
v___y_1435_ = v___y_1450_;
v___y_1436_ = v___x_1451_;
v___y_1437_ = v___x_1451_;
goto v___jp_1434_;
}
case 5:
{
v___y_1435_ = v___y_1450_;
v___y_1436_ = v___x_1451_;
v___y_1437_ = v___x_1451_;
goto v___jp_1434_;
}
case 6:
{
v___y_1435_ = v___y_1450_;
v___y_1436_ = v___x_1451_;
v___y_1437_ = v___x_1451_;
goto v___jp_1434_;
}
default: 
{
lean_object* v___x_1452_; 
lean_inc_ref(v_info_1403_);
v___x_1452_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_1403_);
if (lean_obj_tag(v___x_1452_) == 0)
{
v___y_1435_ = v___y_1450_;
v___y_1436_ = v___x_1451_;
v___y_1437_ = v___y_1450_;
goto v___jp_1434_;
}
else
{
lean_dec_ref_known(v___x_1452_, 1);
v___y_1435_ = v___y_1450_;
v___y_1436_ = v___x_1451_;
v___y_1437_ = v___x_1451_;
goto v___jp_1434_;
}
}
}
}
else
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
lean_dec(v___x_1433_);
lean_dec_ref(v_children_1404_);
lean_dec_ref(v_info_1403_);
lean_dec_ref(v_ctx_1402_);
v___x_1453_ = lean_box(0);
v___x_1454_ = lean_apply_2(v_toPure_1401_, lean_box(0), v___x_1453_);
return v___x_1454_;
}
}
}
v___jp_1408_:
{
lean_object* v_priority_1413_; lean_object* v_result_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v_priority_1413_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_priority_1413_, 0, v___y_1411_);
lean_ctor_set_uint8(v_priority_1413_, sizeof(void*)*1, v___y_1409_);
lean_ctor_set_uint8(v_priority_1413_, sizeof(void*)*1 + 1, v___y_1410_);
lean_ctor_set_uint8(v_priority_1413_, sizeof(void*)*1 + 2, v___y_1412_);
v_result_1414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_result_1414_, 0, v_ctx_1402_);
lean_ctor_set(v_result_1414_, 1, v_info_1403_);
lean_ctor_set(v_result_1414_, 2, v_children_1404_);
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v_priority_1413_);
lean_ctor_set(v___x_1415_, 1, v_result_1414_);
v___x_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
v___x_1417_ = lean_apply_2(v_toPure_1401_, lean_box(0), v___x_1416_);
return v___x_1417_;
}
v___jp_1418_:
{
if (lean_obj_tag(v_info_1403_) == 2)
{
v___y_1409_ = v___y_1419_;
v___y_1410_ = v___y_1423_;
v___y_1411_ = v___y_1422_;
v___y_1412_ = v___y_1421_;
goto v___jp_1408_;
}
else
{
v___y_1409_ = v___y_1419_;
v___y_1410_ = v___y_1423_;
v___y_1411_ = v___y_1422_;
v___y_1412_ = v___y_1420_;
goto v___jp_1408_;
}
}
v___jp_1424_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = lean_box(0);
v___x_1426_ = lean_apply_2(v_toPure_1401_, lean_box(0), v___x_1425_);
return v___x_1426_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1398_ = stack[0].m_obj;
lean_object* v___f_1399_ = stack[1].m_obj;
lean_object* v___x_1400_ = stack[2].m_obj;
lean_object* v_toPure_1401_ = stack[3].m_obj;
lean_object* v_ctx_1402_ = stack[4].m_obj;
lean_object* v_info_1403_ = stack[5].m_obj;
lean_object* v_children_1404_ = stack[6].m_obj;
lean_object* v_hoverPos_1405_ = stack[7].m_obj;
uint8_t v_includeStop_1406_ = stack[8].m_num;
lean_object* v_results_1407_ = stack[9].m_obj;
lean_object* v_res_1462_;
v_res_1462_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3(v___f_1398_, v___f_1399_, v___x_1400_, v_toPure_1401_, v_ctx_1402_, v_info_1403_, v_children_1404_, v_hoverPos_1405_, v_includeStop_1406_, v_results_1407_);
stack->m_obj
 = v_res_1462_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___boxed(lean_object* v___f_1463_, lean_object* v___f_1464_, lean_object* v___x_1465_, lean_object* v_toPure_1466_, lean_object* v_ctx_1467_, lean_object* v_info_1468_, lean_object* v_children_1469_, lean_object* v_hoverPos_1470_, lean_object* v_includeStop_1471_, lean_object* v_results_1472_){
_start:
{
uint8_t v_includeStop_boxed_1473_; lean_object* v_res_1474_; 
v_includeStop_boxed_1473_ = lean_unbox(v_includeStop_1471_);
v_res_1474_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3(v___f_1463_, v___f_1464_, v___x_1465_, v_toPure_1466_, v_ctx_1467_, v_info_1468_, v_children_1469_, v_hoverPos_1470_, v_includeStop_boxed_1473_, v_results_1472_);
lean_dec(v_hoverPos_1470_);
return v_res_1474_;
}
}
lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4(lean_object* v___f_1477_, lean_object* v___f_1478_, lean_object* v___x_1479_, lean_object* v_toPure_1480_, lean_object* v_hoverPos_1481_, uint8_t v_includeStop_1482_, lean_object* v___f_1483_, lean_object* v_filter_1484_, lean_object* v_toBind_1485_, lean_object* v_ctx_1486_, lean_object* v_info_1487_, lean_object* v_children_1488_, lean_object* v_results_1489_){
_start:
{
lean_object* v___x_1490_; lean_object* v___f_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1490_ = lean_box(v_includeStop_1482_);
lean_inc_ref(v_children_1488_);
lean_inc_ref(v_info_1487_);
lean_inc_ref(v_ctx_1486_);
v___f_1491_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_1491_, 0, v___f_1477_);
lean_closure_set(v___f_1491_, 1, v___f_1478_);
lean_closure_set(v___f_1491_, 2, v___x_1479_);
lean_closure_set(v___f_1491_, 3, v_toPure_1480_);
lean_closure_set(v___f_1491_, 4, v_ctx_1486_);
lean_closure_set(v___f_1491_, 5, v_info_1487_);
lean_closure_set(v___f_1491_, 6, v_children_1488_);
lean_closure_set(v___f_1491_, 7, v_hoverPos_1481_);
lean_closure_set(v___f_1491_, 8, v___x_1490_);
v___x_1492_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___closed__0));
v___x_1493_ = l_List_filterMapTR_go___redArg(v___f_1483_, v_results_1489_, v___x_1492_);
v___x_1494_ = lean_apply_4(v_filter_1484_, v_ctx_1486_, v_info_1487_, v_children_1488_, v___x_1493_);
v___x_1495_ = lean_apply_4(v_toBind_1485_, lean_box(0), lean_box(0), v___x_1494_, v___f_1491_);
return v___x_1495_;
}
}
LEAN_EXPORT void l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1477_ = stack[0].m_obj;
lean_object* v___f_1478_ = stack[1].m_obj;
lean_object* v___x_1479_ = stack[2].m_obj;
lean_object* v_toPure_1480_ = stack[3].m_obj;
lean_object* v_hoverPos_1481_ = stack[4].m_obj;
uint8_t v_includeStop_1482_ = stack[5].m_num;
lean_object* v___f_1483_ = stack[6].m_obj;
lean_object* v_filter_1484_ = stack[7].m_obj;
lean_object* v_toBind_1485_ = stack[8].m_obj;
lean_object* v_ctx_1486_ = stack[9].m_obj;
lean_object* v_info_1487_ = stack[10].m_obj;
lean_object* v_children_1488_ = stack[11].m_obj;
lean_object* v_results_1489_ = stack[12].m_obj;
lean_object* v_res_1496_;
v_res_1496_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4(v___f_1477_, v___f_1478_, v___x_1479_, v_toPure_1480_, v_hoverPos_1481_, v_includeStop_1482_, v___f_1483_, v_filter_1484_, v_toBind_1485_, v_ctx_1486_, v_info_1487_, v_children_1488_, v_results_1489_);
stack->m_obj
 = v_res_1496_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___boxed(lean_object* v___f_1497_, lean_object* v___f_1498_, lean_object* v___x_1499_, lean_object* v_toPure_1500_, lean_object* v_hoverPos_1501_, lean_object* v_includeStop_1502_, lean_object* v___f_1503_, lean_object* v_filter_1504_, lean_object* v_toBind_1505_, lean_object* v_ctx_1506_, lean_object* v_info_1507_, lean_object* v_children_1508_, lean_object* v_results_1509_){
_start:
{
uint8_t v_includeStop_boxed_1510_; lean_object* v_res_1511_; 
v_includeStop_boxed_1510_ = lean_unbox(v_includeStop_1502_);
v_res_1511_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4(v___f_1497_, v___f_1498_, v___x_1499_, v_toPure_1500_, v_hoverPos_1501_, v_includeStop_boxed_1510_, v___f_1503_, v_filter_1504_, v_toBind_1505_, v_ctx_1506_, v_info_1507_, v_children_1508_, v_results_1509_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__6(lean_object* v_toPure_1512_, lean_object* v_results_1513_){
_start:
{
if (lean_obj_tag(v_results_1513_) == 0)
{
goto v___jp_1514_;
}
else
{
lean_object* v_val_1517_; 
v_val_1517_ = lean_ctor_get(v_results_1513_, 0);
lean_inc(v_val_1517_);
lean_dec_ref_known(v_results_1513_, 1);
if (lean_obj_tag(v_val_1517_) == 0)
{
goto v___jp_1514_;
}
else
{
lean_object* v_val_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1534_; 
v_val_1518_ = lean_ctor_get(v_val_1517_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_val_1517_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1520_ = v_val_1517_;
v_isShared_1521_ = v_isSharedCheck_1534_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_val_1518_);
lean_dec(v_val_1517_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1534_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v_snd_1522_; lean_object* v_info_1523_; lean_object* v___x_1525_; 
v_snd_1522_ = lean_ctor_get(v_val_1518_, 1);
lean_inc(v_snd_1522_);
lean_dec(v_val_1518_);
v_info_1523_ = lean_ctor_get(v_snd_1522_, 1);
lean_inc_ref(v_info_1523_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v_snd_1522_);
v___x_1525_ = v___x_1520_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_snd_1522_);
v___x_1525_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
if (lean_obj_tag(v_info_1523_) == 1)
{
lean_object* v_i_1526_; lean_object* v_expr_1527_; uint8_t v___x_1528_; 
v_i_1526_ = lean_ctor_get(v_info_1523_, 0);
lean_inc_ref(v_i_1526_);
lean_dec_ref_known(v_info_1523_, 1);
v_expr_1527_ = lean_ctor_get(v_i_1526_, 3);
lean_inc_ref(v_expr_1527_);
lean_dec_ref(v_i_1526_);
v___x_1528_ = l_Lean_Expr_isSyntheticSorry(v_expr_1527_);
lean_dec_ref(v_expr_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_apply_2(v_toPure_1512_, lean_box(0), v___x_1525_);
return v___x_1529_;
}
else
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_dec_ref(v___x_1525_);
v___x_1530_ = lean_box(0);
v___x_1531_ = lean_apply_2(v_toPure_1512_, lean_box(0), v___x_1530_);
return v___x_1531_;
}
}
else
{
lean_object* v___x_1532_; 
lean_dec_ref(v_info_1523_);
v___x_1532_ = lean_apply_2(v_toPure_1512_, lean_box(0), v___x_1525_);
return v___x_1532_;
}
}
}
}
}
v___jp_1514_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_box(0);
v___x_1516_ = lean_apply_2(v_toPure_1512_, lean_box(0), v___x_1515_);
return v___x_1516_;
}
}
}
lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg(lean_object* v_inst_1537_, lean_object* v_t_1538_, lean_object* v_hoverPos_1539_, uint8_t v_includeStop_1540_, lean_object* v_filter_1541_){
_start:
{
lean_object* v_toApplicative_1542_; lean_object* v_toBind_1543_; lean_object* v_toPure_1544_; lean_object* v___f_1545_; lean_object* v___f_1546_; lean_object* v___f_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v_postNode_1550_; lean_object* v___f_1551_; lean_object* v___f_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v_toApplicative_1542_ = lean_ctor_get(v_inst_1537_, 0);
v_toBind_1543_ = lean_ctor_get(v_inst_1537_, 1);
lean_inc_n(v_toBind_1543_, 2);
v_toPure_1544_ = lean_ctor_get(v_toApplicative_1542_, 1);
v___f_1545_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__0));
v___f_1546_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___closed__1));
v___f_1547_ = ((lean_object*)(l_Lean_Elab_instMaxHoverableInfoPrio___closed__0));
v___x_1548_ = ((lean_object*)(l_Lean_Elab_instBEqHoverableInfoPrio___closed__0));
v___x_1549_ = lean_box(v_includeStop_1540_);
lean_inc_n(v_toPure_1544_, 3);
v_postNode_1550_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___boxed), 13, 9);
lean_closure_set(v_postNode_1550_, 0, v___f_1545_);
lean_closure_set(v_postNode_1550_, 1, v___f_1547_);
lean_closure_set(v_postNode_1550_, 2, v___x_1548_);
lean_closure_set(v_postNode_1550_, 3, v_toPure_1544_);
lean_closure_set(v_postNode_1550_, 4, v_hoverPos_1539_);
lean_closure_set(v_postNode_1550_, 5, v___x_1549_);
lean_closure_set(v_postNode_1550_, 6, v___f_1546_);
lean_closure_set(v_postNode_1550_, 7, v_filter_1541_);
lean_closure_set(v_postNode_1550_, 8, v_toBind_1543_);
v___f_1551_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___redArg___lam__2___boxed), 4, 1);
lean_closure_set(v___f_1551_, 0, v_toPure_1544_);
v___f_1552_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__6), 2, 1);
lean_closure_set(v___f_1552_, 0, v_toPure_1544_);
v___x_1553_ = lean_box(0);
v___x_1554_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___redArg(v_inst_1537_, v___f_1551_, v_postNode_1550_, v___x_1553_, v_t_1538_);
v___x_1555_ = lean_apply_4(v_toBind_1543_, lean_box(0), lean_box(0), v___x_1554_, v___f_1552_);
return v___x_1555_;
}
}
LEAN_EXPORT void l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1537_ = stack[0].m_obj;
lean_object* v_t_1538_ = stack[1].m_obj;
lean_object* v_hoverPos_1539_ = stack[2].m_obj;
uint8_t v_includeStop_1540_ = stack[3].m_num;
lean_object* v_filter_1541_ = stack[4].m_obj;
lean_object* v_res_1556_;
v_res_1556_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg(v_inst_1537_, v_t_1538_, v_hoverPos_1539_, v_includeStop_1540_, v_filter_1541_);
stack->m_obj
 = v_res_1556_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___boxed(lean_object* v_inst_1557_, lean_object* v_t_1558_, lean_object* v_hoverPos_1559_, lean_object* v_includeStop_1560_, lean_object* v_filter_1561_){
_start:
{
uint8_t v_includeStop_boxed_1562_; lean_object* v_res_1563_; 
v_includeStop_boxed_1562_ = lean_unbox(v_includeStop_1560_);
v_res_1563_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg(v_inst_1557_, v_t_1558_, v_hoverPos_1559_, v_includeStop_boxed_1562_, v_filter_1561_);
return v_res_1563_;
}
}
lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f(lean_object* v_m_1564_, lean_object* v_inst_1565_, lean_object* v_t_1566_, lean_object* v_hoverPos_1567_, uint8_t v_includeStop_1568_, lean_object* v_filter_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg(v_inst_1565_, v_t_1566_, v_hoverPos_1567_, v_includeStop_1568_, v_filter_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT void l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1565_ = stack[1].m_obj;
lean_object* v_t_1566_ = stack[2].m_obj;
lean_object* v_hoverPos_1567_ = stack[3].m_obj;
uint8_t v_includeStop_1568_ = stack[4].m_num;
lean_object* v_filter_1569_ = stack[5].m_obj;
lean_object* v_res_1571_;
v_res_1571_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f(lean_box(0), v_inst_1565_, v_t_1566_, v_hoverPos_1567_, v_includeStop_1568_, v_filter_1569_);
stack->m_obj
 = v_res_1571_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___boxed(lean_object* v_m_1572_, lean_object* v_inst_1573_, lean_object* v_t_1574_, lean_object* v_hoverPos_1575_, lean_object* v_includeStop_1576_, lean_object* v_filter_1577_){
_start:
{
uint8_t v_includeStop_boxed_1578_; lean_object* v_res_1579_; 
v_includeStop_boxed_1578_ = lean_unbox(v_includeStop_1576_);
v_res_1579_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f(v_m_1572_, v_inst_1573_, v_t_1574_, v_hoverPos_1575_, v_includeStop_boxed_1578_, v_filter_1577_);
return v_res_1579_;
}
}
lean_object* l_Lean_Elab_Info_type_x3f(lean_object* v_i_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
switch(lean_obj_tag(v_i_1580_))
{
case 1:
{
lean_object* v_i_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1611_; 
v_i_1586_ = lean_ctor_get(v_i_1580_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_i_1580_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1588_ = v_i_1580_;
v_isShared_1589_ = v_isSharedCheck_1611_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_i_1586_);
lean_dec(v_i_1580_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1611_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v_expr_1590_; lean_object* v___x_1591_; 
v_expr_1590_ = lean_ctor_get(v_i_1586_, 3);
lean_inc_ref(v_expr_1590_);
lean_dec_ref(v_i_1586_);
lean_inc(v_a_1584_);
lean_inc_ref(v_a_1583_);
lean_inc(v_a_1582_);
lean_inc_ref(v_a_1581_);
v___x_1591_ = lean_infer_type(v_expr_1590_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1602_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1594_ = v___x_1591_;
v_isShared_1595_ = v_isSharedCheck_1602_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1591_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1602_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 0, v_a_1592_);
v___x_1597_ = v___x_1588_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1599_; 
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1597_);
v___x_1599_ = v___x_1594_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_del_object(v___x_1588_);
v_a_1603_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1591_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1591_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
case 7:
{
lean_object* v_i_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1637_; 
v_i_1612_ = lean_ctor_get(v_i_1580_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_i_1580_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1614_ = v_i_1580_;
v_isShared_1615_ = v_isSharedCheck_1637_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_i_1612_);
lean_dec(v_i_1580_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1637_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v_val_1616_; lean_object* v___x_1617_; 
v_val_1616_ = lean_ctor_get(v_i_1612_, 3);
lean_inc_ref(v_val_1616_);
lean_dec_ref(v_i_1612_);
lean_inc(v_a_1584_);
lean_inc_ref(v_a_1583_);
lean_inc(v_a_1582_);
lean_inc_ref(v_a_1581_);
v___x_1617_ = lean_infer_type(v_val_1616_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
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
if (v_isShared_1615_ == 0)
{
lean_ctor_set_tag(v___x_1614_, 1);
lean_ctor_set(v___x_1614_, 0, v_a_1618_);
v___x_1623_ = v___x_1614_;
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
lean_del_object(v___x_1614_);
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
case 13:
{
lean_object* v_i_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1664_; 
v_i_1638_ = lean_ctor_get(v_i_1580_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_i_1580_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1640_ = v_i_1580_;
v_isShared_1641_ = v_isSharedCheck_1664_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_i_1638_);
lean_dec(v_i_1580_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1664_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v_toTermInfo_1642_; lean_object* v_expr_1643_; lean_object* v___x_1644_; 
v_toTermInfo_1642_ = lean_ctor_get(v_i_1638_, 0);
lean_inc_ref(v_toTermInfo_1642_);
lean_dec_ref(v_i_1638_);
v_expr_1643_ = lean_ctor_get(v_toTermInfo_1642_, 3);
lean_inc_ref(v_expr_1643_);
lean_dec_ref(v_toTermInfo_1642_);
lean_inc(v_a_1584_);
lean_inc_ref(v_a_1583_);
lean_inc(v_a_1582_);
lean_inc_ref(v_a_1581_);
v___x_1644_ = lean_infer_type(v_expr_1643_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1655_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1647_ = v___x_1644_;
v_isShared_1648_ = v_isSharedCheck_1655_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1644_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1655_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set_tag(v___x_1640_, 1);
lean_ctor_set(v___x_1640_, 0, v_a_1645_);
v___x_1650_ = v___x_1640_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
lean_object* v___x_1652_; 
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 0, v___x_1650_);
v___x_1652_ = v___x_1647_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_del_object(v___x_1640_);
v_a_1656_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1644_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1644_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
default: 
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
lean_dec_ref(v_i_1580_);
v___x_1665_ = lean_box(0);
v___x_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
return v___x_1666_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Info_type_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1580_ = stack[0].m_obj;
lean_object* v_a_1581_ = stack[1].m_obj;
lean_object* v_a_1582_ = stack[2].m_obj;
lean_object* v_a_1583_ = stack[3].m_obj;
lean_object* v_a_1584_ = stack[4].m_obj;
lean_object* v_res_1667_;
v_res_1667_ = l_Lean_Elab_Info_type_x3f(v_i_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
stack->m_obj
 = v_res_1667_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_type_x3f___boxed(lean_object* v_i_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_Elab_Info_type_x3f(v_i_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
return v_res_1674_;
}
}
lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(lean_object* v_declName_1675_, uint8_t v_includeBuiltin_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___x_1680_; lean_object* v_toCold_1681_; lean_object* v_env_1682_; lean_object* v_ref_1683_; lean_object* v_currNamespace_1684_; lean_object* v_openDecls_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1680_ = lean_st_ref_get(v___y_1678_);
v_toCold_1681_ = lean_ctor_get(v___y_1677_, 0);
v_env_1682_ = lean_ctor_get(v___x_1680_, 0);
lean_inc_ref(v_env_1682_);
lean_dec(v___x_1680_);
v_ref_1683_ = lean_ctor_get(v___y_1677_, 2);
v_currNamespace_1684_ = lean_ctor_get(v_toCold_1681_, 4);
v_openDecls_1685_ = lean_ctor_get(v_toCold_1681_, 5);
v___x_1686_ = l_Lean_Options_empty;
lean_inc(v_openDecls_1685_);
lean_inc(v_currNamespace_1684_);
v___x_1687_ = l_Lean_findDocString_x3f(v_env_1682_, v_declName_1675_, v_includeBuiltin_1676_, v___x_1686_, v_currNamespace_1684_, v_openDecls_1685_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1687_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1707_; 
v_a_1696_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1698_ = v___x_1687_;
v_isShared_1699_ = v_isSharedCheck_1707_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1687_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1707_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1705_; 
v___x_1700_ = lean_io_error_to_string(v_a_1696_);
v___x_1701_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1700_);
v___x_1702_ = l_Lean_MessageData_ofFormat(v___x_1701_);
lean_inc(v_ref_1683_);
v___x_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1703_, 0, v_ref_1683_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 0, v___x_1703_);
v___x_1705_ = v___x_1698_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1703_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1675_ = stack[0].m_obj;
uint8_t v_includeBuiltin_1676_ = stack[1].m_num;
lean_object* v___y_1677_ = stack[2].m_obj;
lean_object* v___y_1678_ = stack[3].m_obj;
lean_object* v_res_1708_;
v_res_1708_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_declName_1675_, v_includeBuiltin_1676_, v___y_1677_, v___y_1678_);
stack->m_obj
 = v_res_1708_;
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg___boxed(lean_object* v_declName_1709_, lean_object* v_includeBuiltin_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
uint8_t v_includeBuiltin_boxed_1714_; lean_object* v_res_1715_; 
v_includeBuiltin_boxed_1714_ = lean_unbox(v_includeBuiltin_1710_);
v_res_1715_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_declName_1709_, v_includeBuiltin_boxed_1714_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
return v_res_1715_;
}
}
lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0(lean_object* v_declName_1716_, uint8_t v_includeBuiltin_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_declName_1716_, v_includeBuiltin_1717_, v___y_1720_, v___y_1721_);
return v___x_1723_;
}
}
LEAN_EXPORT void l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1716_ = stack[0].m_obj;
uint8_t v_includeBuiltin_1717_ = stack[1].m_num;
lean_object* v___y_1718_ = stack[2].m_obj;
lean_object* v___y_1719_ = stack[3].m_obj;
lean_object* v___y_1720_ = stack[4].m_obj;
lean_object* v___y_1721_ = stack[5].m_obj;
lean_object* v_res_1724_;
v_res_1724_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0(v_declName_1716_, v_includeBuiltin_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
stack->m_obj
 = v_res_1724_;
}
LEAN_EXPORT lean_object* l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___boxed(lean_object* v_declName_1725_, lean_object* v_includeBuiltin_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
uint8_t v_includeBuiltin_boxed_1732_; lean_object* v_res_1733_; 
v_includeBuiltin_boxed_1732_ = lean_unbox(v_includeBuiltin_1726_);
v_res_1733_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0(v_declName_1725_, v_includeBuiltin_boxed_1732_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
return v_res_1733_;
}
}
lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg(lean_object* v_name_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v_env_1739_; lean_object* v___x_1740_; lean_object* v_toEnvExtension_1741_; lean_object* v_asyncMode_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1737_ = lean_box(1);
v___x_1738_ = lean_st_ref_get(v___y_1735_);
v_env_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc_ref(v_env_1739_);
lean_dec(v___x_1738_);
v___x_1740_ = l_Lean_errorExplanationExt;
v_toEnvExtension_1741_ = lean_ctor_get(v___x_1740_, 0);
v_asyncMode_1742_ = lean_ctor_get(v_toEnvExtension_1741_, 2);
v___x_1743_ = lean_box(0);
v___x_1744_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1737_, v___x_1740_, v_env_1739_, v_asyncMode_1742_, v___x_1743_);
v___x_1745_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1744_, v_name_1734_);
lean_dec(v___x_1744_);
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT void l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1734_ = stack[0].m_obj;
lean_object* v___y_1735_ = stack[1].m_obj;
lean_object* v_res_1747_;
v_res_1747_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg(v_name_1734_, v___y_1735_);
stack->m_obj
 = v_res_1747_;
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg___boxed(lean_object* v_name_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg(v_name_1748_, v___y_1749_);
lean_dec(v___y_1749_);
lean_dec(v_name_1748_);
return v_res_1751_;
}
}
lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1(lean_object* v_name_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg(v_name_1752_, v___y_1756_);
return v___x_1758_;
}
}
LEAN_EXPORT void l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1752_ = stack[0].m_obj;
lean_object* v___y_1753_ = stack[1].m_obj;
lean_object* v___y_1754_ = stack[2].m_obj;
lean_object* v___y_1755_ = stack[3].m_obj;
lean_object* v___y_1756_ = stack[4].m_obj;
lean_object* v_res_1759_;
v_res_1759_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1(v_name_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
stack->m_obj
 = v_res_1759_;
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___boxed(lean_object* v_name_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1(v_name_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v_name_1760_);
return v_res_1766_;
}
}
lean_object* l_Lean_Elab_Info_docString_x3f(lean_object* v_i_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; 
switch(lean_obj_tag(v_i_1767_))
{
case 1:
{
lean_object* v_i_1789_; lean_object* v_expr_1790_; lean_object* v___x_1791_; 
v_i_1789_ = lean_ctor_get(v_i_1767_, 0);
v_expr_1790_ = lean_ctor_get(v_i_1789_, 3);
v___x_1791_ = l_Lean_Expr_constName_x3f(v_expr_1790_);
if (lean_obj_tag(v___x_1791_) == 1)
{
lean_object* v_val_1792_; uint8_t v___x_1793_; lean_object* v___x_1794_; 
lean_dec_ref_known(v_i_1767_, 1);
v_val_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_val_1792_);
lean_dec_ref_known(v___x_1791_, 1);
v___x_1793_ = 1;
v___x_1794_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_val_1792_, v___x_1793_, v_a_1770_, v_a_1771_);
return v___x_1794_;
}
else
{
lean_dec(v___x_1791_);
v___y_1774_ = v_a_1768_;
v___y_1775_ = v_a_1769_;
v___y_1776_ = v_a_1770_;
v___y_1777_ = v_a_1771_;
goto v___jp_1773_;
}
}
case 13:
{
lean_object* v_i_1795_; lean_object* v___x_1796_; 
v_i_1795_ = lean_ctor_get(v_i_1767_, 0);
v___x_1796_ = l_Lean_Meta_getPPContext(v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v_ref_1798_; lean_object* v___x_1799_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v___x_1796_, 1);
v_ref_1798_ = lean_ctor_get(v_a_1770_, 2);
lean_inc_ref(v_i_1795_);
v___x_1799_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v_a_1797_, v_i_1795_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1813_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1802_ = v___x_1799_;
v_isShared_1803_ = v_isSharedCheck_1813_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1799_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1813_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
if (lean_obj_tag(v_a_1800_) == 1)
{
lean_object* v___x_1805_; 
lean_dec_ref_known(v_i_1767_, 1);
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
else
{
lean_object* v_toTermInfo_1807_; lean_object* v_expr_1808_; lean_object* v___x_1809_; 
lean_del_object(v___x_1802_);
lean_dec(v_a_1800_);
v_toTermInfo_1807_ = lean_ctor_get(v_i_1795_, 0);
v_expr_1808_ = lean_ctor_get(v_toTermInfo_1807_, 3);
v___x_1809_ = l_Lean_Expr_constName_x3f(v_expr_1808_);
if (lean_obj_tag(v___x_1809_) == 1)
{
lean_object* v_val_1810_; uint8_t v___x_1811_; lean_object* v___x_1812_; 
lean_dec_ref_known(v_i_1767_, 1);
v_val_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_val_1810_);
lean_dec_ref_known(v___x_1809_, 1);
v___x_1811_ = 1;
v___x_1812_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_val_1810_, v___x_1811_, v_a_1770_, v_a_1771_);
return v___x_1812_;
}
else
{
lean_dec(v___x_1809_);
v___y_1774_ = v_a_1768_;
v___y_1775_ = v_a_1769_;
v___y_1776_ = v_a_1770_;
v___y_1777_ = v_a_1771_;
goto v___jp_1773_;
}
}
}
}
else
{
lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1831_; 
v_isSharedCheck_1831_ = !lean_is_exclusive(v_i_1767_);
if (v_isSharedCheck_1831_ == 0)
{
lean_object* v_unused_1832_; 
v_unused_1832_ = lean_ctor_get(v_i_1767_, 0);
lean_dec(v_unused_1832_);
v___x_1815_ = v_i_1767_;
v_isShared_1816_ = v_isSharedCheck_1831_;
goto v_resetjp_1814_;
}
else
{
lean_dec(v_i_1767_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1831_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1830_; 
v_a_1817_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1819_ = v___x_1799_;
v_isShared_1820_ = v_isSharedCheck_1830_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1799_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1830_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; lean_object* v___x_1823_; 
v___x_1821_ = lean_io_error_to_string(v_a_1817_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set_tag(v___x_1815_, 3);
lean_ctor_set(v___x_1815_, 0, v___x_1821_);
v___x_1823_ = v___x_1815_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1824_ = l_Lean_MessageData_ofFormat(v___x_1823_);
lean_inc(v_ref_1798_);
v___x_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1825_, 0, v_ref_1798_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1825_);
v___x_1827_ = v___x_1819_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_dec_ref_known(v_i_1767_, 1);
v_a_1833_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1796_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1796_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
case 7:
{
lean_object* v_i_1841_; lean_object* v_projName_1842_; uint8_t v___x_1843_; lean_object* v___x_1844_; 
v_i_1841_ = lean_ctor_get(v_i_1767_, 0);
lean_inc_ref(v_i_1841_);
lean_dec_ref_known(v_i_1767_, 1);
v_projName_1842_ = lean_ctor_get(v_i_1841_, 0);
lean_inc(v_projName_1842_);
lean_dec_ref(v_i_1841_);
v___x_1843_ = 1;
v___x_1844_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_projName_1842_, v___x_1843_, v_a_1770_, v_a_1771_);
return v___x_1844_;
}
case 5:
{
lean_object* v_i_1845_; lean_object* v_optionName_1846_; lean_object* v_declName_1847_; uint8_t v___x_1848_; lean_object* v___x_1849_; 
v_i_1845_ = lean_ctor_get(v_i_1767_, 0);
lean_inc_ref(v_i_1845_);
lean_dec_ref_known(v_i_1767_, 1);
v_optionName_1846_ = lean_ctor_get(v_i_1845_, 1);
lean_inc(v_optionName_1846_);
v_declName_1847_ = lean_ctor_get(v_i_1845_, 2);
lean_inc(v_declName_1847_);
lean_dec_ref(v_i_1845_);
v___x_1848_ = 1;
v___x_1849_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_declName_1847_, v___x_1848_, v_a_1770_, v_a_1771_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
if (lean_obj_tag(v_a_1850_) == 1)
{
lean_dec(v_optionName_1846_);
return v___x_1849_;
}
else
{
lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1892_; 
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1892_ == 0)
{
lean_object* v_unused_1893_; 
v_unused_1893_ = lean_ctor_get(v___x_1849_, 0);
lean_dec(v_unused_1893_);
v___x_1852_ = v___x_1849_;
v_isShared_1853_ = v_isSharedCheck_1892_;
goto v_resetjp_1851_;
}
else
{
lean_dec(v___x_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1892_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v_ref_1854_; lean_object* v___x_1855_; 
v_ref_1854_ = lean_ctor_get(v_a_1770_, 2);
v___x_1855_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1877_; 
lean_del_object(v___x_1852_);
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1858_ = v___x_1855_;
v_isShared_1859_ = v_isSharedCheck_1877_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1855_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1877_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1856_, v_optionName_1846_);
lean_dec(v_optionName_1846_);
lean_dec(v_a_1856_);
if (lean_obj_tag(v___x_1860_) == 1)
{
lean_object* v_val_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1872_; 
v_val_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1872_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_val_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1872_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1865_ = l_Lean_OptionDecl_fullDescr(v_val_1861_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1865_);
v___x_1867_ = v___x_1863_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1869_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1867_);
v___x_1869_ = v___x_1858_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
else
{
lean_object* v___x_1873_; lean_object* v___x_1875_; 
lean_dec(v___x_1860_);
v___x_1873_ = lean_box(0);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1873_);
v___x_1875_ = v___x_1858_;
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
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1891_; 
lean_dec(v_optionName_1846_);
v_a_1878_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1880_ = v___x_1855_;
v_isShared_1881_ = v_isSharedCheck_1891_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1855_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1891_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1882_ = lean_io_error_to_string(v_a_1878_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set_tag(v___x_1852_, 3);
lean_ctor_set(v___x_1852_, 0, v___x_1882_);
v___x_1884_ = v___x_1852_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1885_ = l_Lean_MessageData_ofFormat(v___x_1884_);
lean_inc(v_ref_1854_);
v___x_1886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1886_, 0, v_ref_1854_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1886_);
v___x_1888_ = v___x_1880_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
}
}
}
else
{
lean_dec(v_optionName_1846_);
return v___x_1849_;
}
}
case 6:
{
lean_object* v_i_1894_; lean_object* v_errorName_1895_; lean_object* v___x_1896_; lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1917_; 
v_i_1894_ = lean_ctor_get(v_i_1767_, 0);
lean_inc_ref(v_i_1894_);
lean_dec_ref_known(v_i_1767_, 1);
v_errorName_1895_ = lean_ctor_get(v_i_1894_, 1);
lean_inc(v_errorName_1895_);
lean_dec_ref(v_i_1894_);
v___x_1896_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_Info_docString_x3f_spec__1___redArg(v_errorName_1895_, v_a_1771_);
lean_dec(v_errorName_1895_);
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1899_ = v___x_1896_;
v_isShared_1900_ = v_isSharedCheck_1917_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1896_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1917_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
if (lean_obj_tag(v_a_1897_) == 1)
{
lean_object* v_val_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1912_; 
v_val_1901_ = lean_ctor_get(v_a_1897_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_a_1897_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1903_ = v_a_1897_;
v_isShared_1904_ = v_isSharedCheck_1912_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_val_1901_);
lean_dec(v_a_1897_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1912_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1905_ = l_Lean_ErrorExplanation_summaryWithSeverity(v_val_1901_);
lean_dec(v_val_1901_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1905_);
v___x_1907_ = v___x_1903_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1909_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1907_);
v___x_1909_ = v___x_1899_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
else
{
lean_object* v___x_1913_; lean_object* v___x_1915_; 
lean_dec(v_a_1897_);
v___x_1913_ = lean_box(0);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1913_);
v___x_1915_ = v___x_1899_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
case 16:
{
lean_object* v_i_1918_; lean_object* v_stx_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; lean_object* v___x_1922_; 
v_i_1918_ = lean_ctor_get(v_i_1767_, 0);
lean_inc_ref(v_i_1918_);
lean_dec_ref_known(v_i_1767_, 1);
v_stx_1919_ = lean_ctor_get(v_i_1918_, 1);
lean_inc(v_stx_1919_);
lean_dec_ref(v_i_1918_);
v___x_1920_ = l_Lean_Syntax_getKind(v_stx_1919_);
v___x_1921_ = 1;
v___x_1922_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v___x_1920_, v___x_1921_, v_a_1770_, v_a_1771_);
return v___x_1922_;
}
case 17:
{
lean_object* v_i_1923_; lean_object* v_name_1924_; uint8_t v___x_1925_; lean_object* v___x_1926_; 
v_i_1923_ = lean_ctor_get(v_i_1767_, 0);
lean_inc_ref(v_i_1923_);
lean_dec_ref_known(v_i_1767_, 1);
v_name_1924_ = lean_ctor_get(v_i_1923_, 1);
lean_inc(v_name_1924_);
lean_dec_ref(v_i_1923_);
v___x_1925_ = 1;
v___x_1926_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_name_1924_, v___x_1925_, v_a_1770_, v_a_1771_);
return v___x_1926_;
}
default: 
{
v___y_1774_ = v_a_1768_;
v___y_1775_ = v_a_1769_;
v___y_1776_ = v_a_1770_;
v___y_1777_ = v_a_1771_;
goto v___jp_1773_;
}
}
v___jp_1773_:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_Elab_Info_toElabInfo_x3f(v_i_1767_);
if (lean_obj_tag(v___x_1778_) == 1)
{
lean_object* v_val_1779_; lean_object* v_elaborator_1780_; lean_object* v_stx_1781_; lean_object* v___x_1782_; uint8_t v___x_1783_; lean_object* v___x_1784_; 
v_val_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_val_1779_);
lean_dec_ref_known(v___x_1778_, 1);
v_elaborator_1780_ = lean_ctor_get(v_val_1779_, 0);
lean_inc(v_elaborator_1780_);
v_stx_1781_ = lean_ctor_get(v_val_1779_, 1);
lean_inc(v_stx_1781_);
lean_dec(v_val_1779_);
v___x_1782_ = l_Lean_Syntax_getKind(v_stx_1781_);
v___x_1783_ = 1;
v___x_1784_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v___x_1782_, v___x_1783_, v___y_1776_, v___y_1777_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
if (lean_obj_tag(v_a_1785_) == 0)
{
lean_object* v___x_1786_; 
lean_dec_ref_known(v___x_1784_, 1);
v___x_1786_ = l_Lean_findMarkdownDocString_x3f___at___00Lean_Elab_Info_docString_x3f_spec__0___redArg(v_elaborator_1780_, v___x_1783_, v___y_1776_, v___y_1777_);
return v___x_1786_;
}
else
{
lean_dec(v_elaborator_1780_);
return v___x_1784_;
}
}
else
{
lean_dec(v_elaborator_1780_);
return v___x_1784_;
}
}
else
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
lean_dec(v___x_1778_);
v___x_1787_ = lean_box(0);
v___x_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
return v___x_1788_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Info_docString_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1767_ = stack[0].m_obj;
lean_object* v_a_1768_ = stack[1].m_obj;
lean_object* v_a_1769_ = stack[2].m_obj;
lean_object* v_a_1770_ = stack[3].m_obj;
lean_object* v_a_1771_ = stack[4].m_obj;
lean_object* v_res_1927_;
v_res_1927_ = l_Lean_Elab_Info_docString_x3f(v_i_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_);
stack->m_obj
 = v_res_1927_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_docString_x3f___boxed(lean_object* v_i_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_Elab_Info_docString_x3f(v_i_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
return v_res_1934_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1935_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
return v___x_1937_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1938_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1939_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1940_ = lean_unsigned_to_nat(0u);
v___x_1941_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
lean_ctor_set(v___x_1941_, 2, v___x_1940_);
lean_ctor_set(v___x_1941_, 3, v___x_1940_);
lean_ctor_set(v___x_1941_, 4, v___x_1939_);
lean_ctor_set(v___x_1941_, 5, v___x_1939_);
lean_ctor_set(v___x_1941_, 6, v___x_1939_);
lean_ctor_set(v___x_1941_, 7, v___x_1939_);
lean_ctor_set(v___x_1941_, 8, v___x_1939_);
lean_ctor_set(v___x_1941_, 9, v___x_1939_);
lean_ctor_set(v___x_1941_, 10, v___x_1939_);
lean_ctor_set(v___x_1941_, 11, v___x_1938_);
return v___x_1941_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1942_ = lean_unsigned_to_nat(32u);
v___x_1943_ = lean_mk_empty_array_with_capacity(v___x_1942_);
v___x_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
return v___x_1944_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1945_ = ((size_t)5ULL);
v___x_1946_ = lean_unsigned_to_nat(0u);
v___x_1947_ = lean_unsigned_to_nat(32u);
v___x_1948_ = lean_mk_empty_array_with_capacity(v___x_1947_);
v___x_1949_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1950_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
lean_ctor_set(v___x_1950_, 1, v___x_1948_);
lean_ctor_set(v___x_1950_, 2, v___x_1946_);
lean_ctor_set(v___x_1950_, 3, v___x_1946_);
lean_ctor_set_usize(v___x_1950_, 4, v___x_1945_);
return v___x_1950_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1951_ = lean_box(1);
v___x_1952_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_1953_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1954_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
lean_ctor_set(v___x_1954_, 1, v___x_1952_);
lean_ctor_set(v___x_1954_, 2, v___x_1951_);
return v___x_1954_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1957_ = l_Lean_stringToMessageData(v___x_1956_);
return v___x_1957_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1960_ = l_Lean_stringToMessageData(v___x_1959_);
return v___x_1960_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1963_ = l_Lean_stringToMessageData(v___x_1962_);
return v___x_1963_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1966_ = l_Lean_stringToMessageData(v___x_1965_);
return v___x_1966_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_1969_ = l_Lean_stringToMessageData(v___x_1968_);
return v___x_1969_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_1972_ = l_Lean_stringToMessageData(v___x_1971_);
return v___x_1972_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_1975_ = l_Lean_stringToMessageData(v___x_1974_);
return v___x_1975_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__21(void){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__20));
v___x_1978_ = l_Lean_stringToMessageData(v___x_1977_);
return v___x_1978_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__23(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__22));
v___x_1981_ = l_Lean_stringToMessageData(v___x_1980_);
return v___x_1981_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__25(void){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__24));
v___x_1984_ = l_Lean_stringToMessageData(v___x_1983_);
return v___x_1984_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__27(void){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__26));
v___x_1987_ = l_Lean_stringToMessageData(v___x_1986_);
return v___x_1987_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1988_, lean_object* v_declHint_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v_env_1994_; uint8_t v___x_1995_; 
v___x_1992_ = lean_box(0);
v___x_1993_ = lean_st_ref_get(v___y_1990_);
v_env_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc_ref(v_env_1994_);
lean_dec(v___x_1993_);
v___x_1995_ = l_Lean_Name_isAnonymous(v_declHint_1989_);
if (v___x_1995_ == 0)
{
uint8_t v_isExporting_1996_; 
v_isExporting_1996_ = lean_ctor_get_uint8(v_env_1994_, sizeof(void*)*13);
if (v_isExporting_1996_ == 0)
{
lean_object* v___x_1997_; 
lean_dec_ref(v_env_1994_);
lean_dec(v_declHint_1989_);
v___x_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1997_, 0, v_msg_1988_);
return v___x_1997_;
}
else
{
lean_object* v___x_1998_; uint8_t v___x_1999_; 
lean_inc_ref(v_env_1994_);
v___x_1998_ = l_Lean_Environment_setExporting(v_env_1994_, v___x_1995_);
lean_inc(v_declHint_1989_);
lean_inc_ref(v___x_1998_);
v___x_1999_ = l_Lean_Environment_contains(v___x_1998_, v_declHint_1989_, v_isExporting_1996_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; 
lean_dec_ref(v___x_1998_);
lean_dec_ref(v_env_1994_);
lean_dec(v_declHint_1989_);
v___x_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2000_, 0, v_msg_1988_);
return v___x_2000_;
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v_c_2006_; lean_object* v___x_2007_; 
v___x_2001_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_2002_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_2003_ = l_Lean_Options_empty;
v___x_2004_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2004_, 0, v___x_1998_);
lean_ctor_set(v___x_2004_, 1, v___x_2001_);
lean_ctor_set(v___x_2004_, 2, v___x_2002_);
lean_ctor_set(v___x_2004_, 3, v___x_2003_);
lean_inc(v_declHint_1989_);
v___x_2005_ = l_Lean_MessageData_ofConstName(v_declHint_1989_, v___x_1995_);
v_c_2006_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2006_, 0, v___x_2004_);
lean_ctor_set(v_c_2006_, 1, v___x_2005_);
v___x_2007_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1994_, v_declHint_1989_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_dec_ref(v_env_1994_);
lean_dec(v_declHint_1989_);
v___x_2008_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2008_);
lean_ctor_set(v___x_2009_, 1, v_c_2006_);
v___x_2010_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_2011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2009_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = l_Lean_MessageData_note(v___x_2011_);
v___x_2013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2013_, 0, v_msg_1988_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
return v___x_2014_;
}
else
{
lean_object* v_val_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2071_; 
v_val_2015_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2017_ = v___x_2007_;
v_isShared_2018_ = v_isSharedCheck_2071_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_val_2015_);
lean_dec(v___x_2007_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2071_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v_modules_2020_; lean_object* v_moduleNames_2021_; lean_object* v_mod_2022_; uint8_t v___y_2024_; uint8_t v___x_2054_; 
v___x_2019_ = l_Lean_Environment_header(v_env_1994_);
lean_dec_ref(v_env_1994_);
v_modules_2020_ = lean_ctor_get(v___x_2019_, 3);
lean_inc_ref(v_modules_2020_);
v_moduleNames_2021_ = lean_ctor_get(v___x_2019_, 4);
lean_inc_ref(v_moduleNames_2021_);
lean_dec_ref(v___x_2019_);
v_mod_2022_ = lean_array_get(v___x_1992_, v_moduleNames_2021_, v_val_2015_);
lean_dec_ref(v_moduleNames_2021_);
v___x_2054_ = l_Lean_isPrivateName(v_declHint_1989_);
lean_dec(v_declHint_1989_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; uint8_t v___x_2056_; 
v___x_2055_ = lean_array_get_size(v_modules_2020_);
v___x_2056_ = lean_nat_dec_lt(v_val_2015_, v___x_2055_);
if (v___x_2056_ == 0)
{
lean_dec_ref(v_modules_2020_);
lean_dec(v_val_2015_);
v___y_2024_ = v___x_2054_;
goto v___jp_2023_;
}
else
{
lean_object* v___x_2057_; lean_object* v_toImport_2058_; uint8_t v_isExported_2059_; 
v___x_2057_ = lean_array_fget(v_modules_2020_, v_val_2015_);
lean_dec(v_val_2015_);
lean_dec_ref(v_modules_2020_);
v_toImport_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc_ref(v_toImport_2058_);
lean_dec(v___x_2057_);
v_isExported_2059_ = lean_ctor_get_uint8(v_toImport_2058_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2058_);
v___y_2024_ = v_isExported_2059_;
goto v___jp_2023_;
}
}
else
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
lean_dec_ref(v_modules_2020_);
lean_del_object(v___x_2017_);
lean_dec(v_val_2015_);
v___x_2060_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
lean_ctor_set(v___x_2061_, 1, v_c_2006_);
v___x_2062_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__25);
v___x_2063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2061_);
lean_ctor_set(v___x_2063_, 1, v___x_2062_);
v___x_2064_ = l_Lean_MessageData_ofName(v_mod_2022_);
v___x_2065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2063_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__27);
v___x_2067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2065_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
v___x_2068_ = l_Lean_MessageData_note(v___x_2067_);
v___x_2069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2069_, 0, v_msg_1988_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
return v___x_2070_;
}
v___jp_2023_:
{
if (v___y_2024_ == 0)
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2036_; 
v___x_2025_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_2026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
lean_ctor_set(v___x_2026_, 1, v_c_2006_);
v___x_2027_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_2028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2026_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
v___x_2029_ = l_Lean_MessageData_ofName(v_mod_2022_);
v___x_2030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2028_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_2032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2030_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = l_Lean_MessageData_note(v___x_2032_);
v___x_2034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2034_, 0, v_msg_1988_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set_tag(v___x_2017_, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2034_);
v___x_2036_ = v___x_2017_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2052_; 
v___x_2038_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_2039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
lean_ctor_set(v___x_2039_, 1, v_c_2006_);
v___x_2040_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_2041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2039_);
lean_ctor_set(v___x_2041_, 1, v___x_2040_);
v___x_2042_ = l_Lean_MessageData_ofName(v_mod_2022_);
lean_inc_ref(v___x_2042_);
v___x_2043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2041_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
v___x_2044_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__21);
v___x_2045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2043_);
lean_ctor_set(v___x_2045_, 1, v___x_2044_);
v___x_2046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
lean_ctor_set(v___x_2046_, 1, v___x_2042_);
v___x_2047_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__23);
v___x_2048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2046_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
v___x_2049_ = l_Lean_MessageData_note(v___x_2048_);
v___x_2050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2050_, 0, v_msg_1988_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set_tag(v___x_2017_, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2050_);
v___x_2052_ = v___x_2017_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
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
lean_object* v___x_2072_; 
lean_dec_ref(v_env_1994_);
lean_dec(v_declHint_1989_);
v___x_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2072_, 0, v_msg_1988_);
return v___x_2072_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1988_ = stack[0].m_obj;
lean_object* v_declHint_1989_ = stack[1].m_obj;
lean_object* v___y_1990_ = stack[2].m_obj;
lean_object* v_res_2073_;
v_res_2073_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1988_, v_declHint_1989_, v___y_1990_);
stack->m_obj
 = v_res_2073_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_2074_, lean_object* v_declHint_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_2074_, v_declHint_2075_, v___y_2076_);
lean_dec(v___y_2076_);
return v_res_2078_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_2079_, lean_object* v_declHint_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v___x_2086_; lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2096_; 
v___x_2086_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_2079_, v_declHint_2080_, v___y_2084_);
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2089_ = v___x_2086_;
v_isShared_2090_ = v_isSharedCheck_2096_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2086_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2096_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2094_; 
v___x_2091_ = l_Lean_unknownIdentifierMessageTag;
v___x_2092_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v_a_2087_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v___x_2092_);
v___x_2094_ = v___x_2089_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2079_ = stack[0].m_obj;
lean_object* v_declHint_2080_ = stack[1].m_obj;
lean_object* v___y_2081_ = stack[2].m_obj;
lean_object* v___y_2082_ = stack[3].m_obj;
lean_object* v___y_2083_ = stack[4].m_obj;
lean_object* v___y_2084_ = stack[5].m_obj;
lean_object* v_res_2097_;
v_res_2097_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2079_, v_declHint_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
stack->m_obj
 = v_res_2097_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_2098_, lean_object* v_declHint_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2098_, v_declHint_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
return v_res_2105_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object* v_msgData_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v___x_2112_; lean_object* v_env_2113_; uint8_t v___x_2114_; lean_object* v_env_2115_; lean_object* v___x_2116_; lean_object* v_toCold_2117_; lean_object* v_mctx_2118_; lean_object* v_lctx_2119_; lean_object* v_options_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2112_ = lean_st_ref_get(v___y_2110_);
v_env_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc_ref(v_env_2113_);
lean_dec(v___x_2112_);
v___x_2114_ = 0;
v_env_2115_ = l_Lean_Environment_setRecordingDeps(v_env_2113_, v___x_2114_);
v___x_2116_ = lean_st_ref_get(v___y_2108_);
v_toCold_2117_ = lean_ctor_get(v___y_2109_, 0);
v_mctx_2118_ = lean_ctor_get(v___x_2116_, 0);
lean_inc_ref(v_mctx_2118_);
lean_dec(v___x_2116_);
v_lctx_2119_ = lean_ctor_get(v___y_2107_, 2);
v_options_2120_ = lean_ctor_get(v_toCold_2117_, 2);
lean_inc_ref(v_options_2120_);
lean_inc_ref(v_lctx_2119_);
v___x_2121_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2121_, 0, v_env_2115_);
lean_ctor_set(v___x_2121_, 1, v_mctx_2118_);
lean_ctor_set(v___x_2121_, 2, v_lctx_2119_);
lean_ctor_set(v___x_2121_, 3, v_options_2120_);
v___x_2122_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
lean_ctor_set(v___x_2122_, 1, v_msgData_2106_);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2106_ = stack[0].m_obj;
lean_object* v___y_2107_ = stack[1].m_obj;
lean_object* v___y_2108_ = stack[2].m_obj;
lean_object* v___y_2109_ = stack[3].m_obj;
lean_object* v___y_2110_ = stack[4].m_obj;
lean_object* v_res_2124_;
v_res_2124_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
stack->m_obj
 = v_res_2124_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
return v_res_2131_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_ref_2138_; lean_object* v___x_2139_; lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2148_; 
v_ref_2138_ = lean_ctor_get(v___y_2135_, 2);
v___x_2139_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2142_ = v___x_2139_;
v_isShared_2143_ = v_isSharedCheck_2148_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2148_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2144_; lean_object* v___x_2146_; 
lean_inc(v_ref_2138_);
v___x_2144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2144_, 0, v_ref_2138_);
lean_ctor_set(v___x_2144_, 1, v_a_2140_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set_tag(v___x_2142_, 1);
lean_ctor_set(v___x_2142_, 0, v___x_2144_);
v___x_2146_ = v___x_2142_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2144_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2132_ = stack[0].m_obj;
lean_object* v___y_2133_ = stack[1].m_obj;
lean_object* v___y_2134_ = stack[2].m_obj;
lean_object* v___y_2135_ = stack[3].m_obj;
lean_object* v___y_2136_ = stack[4].m_obj;
lean_object* v_res_2149_;
v_res_2149_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
stack->m_obj
 = v_res_2149_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
return v_res_2156_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_2157_, lean_object* v_msg_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_toCold_2164_; lean_object* v_currRecDepth_2165_; lean_object* v_ref_2166_; uint16_t v_optionFlags_2167_; uint8_t v_suppressElabErrors_2168_; uint8_t v_isRecordingDeps_2169_; lean_object* v_ref_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v_toCold_2164_ = lean_ctor_get(v___y_2161_, 0);
v_currRecDepth_2165_ = lean_ctor_get(v___y_2161_, 1);
v_ref_2166_ = lean_ctor_get(v___y_2161_, 2);
v_optionFlags_2167_ = lean_ctor_get_uint16(v___y_2161_, sizeof(void*)*3);
v_suppressElabErrors_2168_ = lean_ctor_get_uint8(v___y_2161_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2169_ = lean_ctor_get_uint8(v___y_2161_, sizeof(void*)*3 + 3);
v_ref_2170_ = l_Lean_replaceRef(v_ref_2157_, v_ref_2166_);
lean_inc(v_currRecDepth_2165_);
lean_inc_ref(v_toCold_2164_);
v___x_2171_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2171_, 0, v_toCold_2164_);
lean_ctor_set(v___x_2171_, 1, v_currRecDepth_2165_);
lean_ctor_set(v___x_2171_, 2, v_ref_2170_);
lean_ctor_set_uint16(v___x_2171_, sizeof(void*)*3, v_optionFlags_2167_);
lean_ctor_set_uint8(v___x_2171_, sizeof(void*)*3 + 2, v_suppressElabErrors_2168_);
lean_ctor_set_uint8(v___x_2171_, sizeof(void*)*3 + 3, v_isRecordingDeps_2169_);
v___x_2172_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_2158_, v___y_2159_, v___y_2160_, v___x_2171_, v___y_2162_);
lean_dec_ref_known(v___x_2171_, 3);
return v___x_2172_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2157_ = stack[0].m_obj;
lean_object* v_msg_2158_ = stack[1].m_obj;
lean_object* v___y_2159_ = stack[2].m_obj;
lean_object* v___y_2160_ = stack[3].m_obj;
lean_object* v___y_2161_ = stack[4].m_obj;
lean_object* v___y_2162_ = stack[5].m_obj;
lean_object* v_res_2173_;
v_res_2173_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_2157_, v_msg_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
stack->m_obj
 = v_res_2173_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_2174_, lean_object* v_msg_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_2174_, v_msg_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v_ref_2174_);
return v_res_2181_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_2182_, lean_object* v_msg_2183_, lean_object* v_declHint_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v___x_2190_; lean_object* v_a_2191_; lean_object* v___x_2192_; 
v___x_2190_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2183_, v_declHint_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref(v___x_2190_);
v___x_2192_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_2182_, v_a_2191_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
return v___x_2192_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2182_ = stack[0].m_obj;
lean_object* v_msg_2183_ = stack[1].m_obj;
lean_object* v_declHint_2184_ = stack[2].m_obj;
lean_object* v___y_2185_ = stack[3].m_obj;
lean_object* v___y_2186_ = stack[4].m_obj;
lean_object* v___y_2187_ = stack[5].m_obj;
lean_object* v___y_2188_ = stack[6].m_obj;
lean_object* v_res_2193_;
v_res_2193_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_2182_, v_msg_2183_, v_declHint_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
stack->m_obj
 = v_res_2193_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_2194_, lean_object* v_msg_2195_, lean_object* v_declHint_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_2194_, v_msg_2195_, v_declHint_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v_ref_2194_);
return v_res_2202_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_2205_ = l_Lean_stringToMessageData(v___x_2204_);
return v___x_2205_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2));
v___x_2208_ = l_Lean_stringToMessageData(v___x_2207_);
return v___x_2208_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_2209_, lean_object* v_constName_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v___x_2216_; uint8_t v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2216_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_2217_ = 0;
lean_inc(v_constName_2210_);
v___x_2218_ = l_Lean_MessageData_ofConstName(v_constName_2210_, v___x_2217_);
v___x_2219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2216_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
v___x_2220_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_2221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2219_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
v___x_2222_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_2209_, v___x_2221_, v_constName_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
return v___x_2222_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2209_ = stack[0].m_obj;
lean_object* v_constName_2210_ = stack[1].m_obj;
lean_object* v___y_2211_ = stack[2].m_obj;
lean_object* v___y_2212_ = stack[3].m_obj;
lean_object* v___y_2213_ = stack[4].m_obj;
lean_object* v___y_2214_ = stack[5].m_obj;
lean_object* v_res_2223_;
v_res_2223_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2209_, v_constName_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
stack->m_obj
 = v_res_2223_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_2224_, lean_object* v_constName_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2224_, v_constName_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v_ref_2224_);
return v_res_2231_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v_ref_2238_; lean_object* v___x_2239_; 
v_ref_2238_ = lean_ctor_get(v___y_2235_, 2);
v___x_2239_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2238_, v_constName_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
return v___x_2239_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2232_ = stack[0].m_obj;
lean_object* v___y_2233_ = stack[1].m_obj;
lean_object* v___y_2234_ = stack[2].m_obj;
lean_object* v___y_2235_ = stack[3].m_obj;
lean_object* v___y_2236_ = stack[4].m_obj;
lean_object* v_res_2240_;
v_res_2240_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
stack->m_obj
 = v_res_2240_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
return v_res_2247_;
}
}
lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(lean_object* v_constName_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v___x_2254_; lean_object* v_env_2255_; uint8_t v___x_2256_; lean_object* v___x_2257_; 
v___x_2254_ = lean_st_ref_get(v___y_2252_);
v_env_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc_ref(v_env_2255_);
lean_dec(v___x_2254_);
v___x_2256_ = 0;
lean_inc(v_constName_2248_);
v___x_2257_ = l_Lean_Environment_find_x3f(v_env_2255_, v_constName_2248_, v___x_2256_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v___x_2258_; 
v___x_2258_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
return v___x_2258_;
}
else
{
lean_object* v_val_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_dec(v_constName_2248_);
v_val_2259_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2257_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_val_2259_);
lean_dec(v___x_2257_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set_tag(v___x_2261_, 0);
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_val_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2248_ = stack[0].m_obj;
lean_object* v___y_2249_ = stack[1].m_obj;
lean_object* v___y_2250_ = stack[2].m_obj;
lean_object* v___y_2251_ = stack[3].m_obj;
lean_object* v___y_2252_ = stack[4].m_obj;
lean_object* v_res_2267_;
v_res_2267_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(v_constName_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
stack->m_obj
 = v_res_2267_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0___boxed(lean_object* v_constName_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(v_constName_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
return v_res_2274_;
}
}
lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(lean_object* v_declName_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = lean_box(0);
lean_inc(v_declName_2275_);
v___x_2282_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0(v_declName_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2308_; 
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2308_ == 0)
{
lean_object* v_unused_2309_; 
v_unused_2309_ = lean_ctor_get(v___x_2282_, 0);
lean_dec(v_unused_2309_);
v___x_2284_ = v___x_2282_;
v_isShared_2285_ = v_isSharedCheck_2308_;
goto v_resetjp_2283_;
}
else
{
lean_dec(v___x_2282_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2308_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; lean_object* v_env_2287_; lean_object* v___x_2288_; 
v___x_2286_ = lean_st_ref_get(v___y_2279_);
v_env_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc_ref(v_env_2287_);
lean_dec(v___x_2286_);
v___x_2288_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2287_, v_declName_2275_);
lean_dec(v_declName_2275_);
lean_dec_ref(v_env_2287_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v___x_2289_; lean_object* v___x_2291_; 
v___x_2289_ = lean_box(0);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2289_);
v___x_2291_ = v___x_2284_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2289_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
else
{
lean_object* v_val_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2307_; 
v_val_2293_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2295_ = v___x_2288_;
v_isShared_2296_ = v_isSharedCheck_2307_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_val_2293_);
lean_dec(v___x_2288_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2307_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2297_; lean_object* v_env_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2297_ = lean_st_ref_get(v___y_2279_);
v_env_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc_ref(v_env_2298_);
lean_dec(v___x_2297_);
v___x_2299_ = l_Lean_Environment_allImportedModuleNames(v_env_2298_);
lean_dec_ref(v_env_2298_);
v___x_2300_ = lean_array_get(v___x_2281_, v___x_2299_, v_val_2293_);
lean_dec(v_val_2293_);
lean_dec_ref(v___x_2299_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v___x_2300_);
v___x_2302_ = v___x_2295_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2304_; 
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2302_);
v___x_2304_ = v___x_2284_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec(v_declName_2275_);
v_a_2310_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2282_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2282_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2275_ = stack[0].m_obj;
lean_object* v___y_2276_ = stack[1].m_obj;
lean_object* v___y_2277_ = stack[2].m_obj;
lean_object* v___y_2278_ = stack[3].m_obj;
lean_object* v___y_2279_ = stack[4].m_obj;
lean_object* v_res_2318_;
v_res_2318_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(v_declName_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
stack->m_obj
 = v_res_2318_;
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0___boxed(lean_object* v_declName_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(v_declName_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
return v_res_2325_;
}
}
lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(lean_object* v_decl_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0(v_decl_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2365_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2341_ = v___x_2338_;
v_isShared_2342_ = v_isSharedCheck_2365_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2338_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2365_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
if (lean_obj_tag(v_a_2339_) == 1)
{
lean_object* v_val_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2360_; 
v_val_2343_ = lean_ctor_get(v_a_2339_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_a_2339_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2345_ = v_a_2339_;
v_isShared_2346_ = v_isSharedCheck_2360_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_val_2343_);
lean_dec(v_a_2339_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2360_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2347_; uint8_t v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2355_; 
v___x_2347_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__1));
v___x_2348_ = 1;
v___x_2349_ = l_Lean_Name_toString(v_val_2343_, v___x_2348_);
v___x_2350_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
v___x_2351_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2347_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
v___x_2352_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___closed__3));
v___x_2353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2351_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v___x_2353_);
v___x_2355_ = v___x_2345_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v___x_2357_; 
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 0, v___x_2355_);
v___x_2357_ = v___x_2341_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
else
{
lean_object* v___x_2361_; lean_object* v___x_2363_; 
lean_dec(v_a_2339_);
v___x_2361_ = lean_box(0);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 0, v___x_2361_);
v___x_2363_ = v___x_2341_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
v_a_2366_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2338_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2338_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_2332_ = stack[0].m_obj;
lean_object* v_a_2333_ = stack[1].m_obj;
lean_object* v_a_2334_ = stack[2].m_obj;
lean_object* v_a_2335_ = stack[3].m_obj;
lean_object* v_a_2336_ = stack[4].m_obj;
lean_object* v_res_2374_;
v_res_2374_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(v_decl_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
stack->m_obj
 = v_res_2374_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___boxed(lean_object* v_decl_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(v_decl_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
return v_res_2381_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2382_, lean_object* v_constName_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
return v___x_2389_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2383_ = stack[1].m_obj;
lean_object* v___y_2384_ = stack[2].m_obj;
lean_object* v___y_2385_ = stack[3].m_obj;
lean_object* v___y_2386_ = stack[4].m_obj;
lean_object* v___y_2387_ = stack[5].m_obj;
lean_object* v_res_2390_;
v_res_2390_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1(lean_box(0), v_constName_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
stack->m_obj
 = v_res_2390_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2391_, lean_object* v_constName_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1(v_00_u03b1_2391_, v_constName_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
return v_res_2398_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2399_, lean_object* v_ref_2400_, lean_object* v_constName_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2400_, v_constName_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2407_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2400_ = stack[1].m_obj;
lean_object* v_constName_2401_ = stack[2].m_obj;
lean_object* v___y_2402_ = stack[3].m_obj;
lean_object* v___y_2403_ = stack[4].m_obj;
lean_object* v___y_2404_ = stack[5].m_obj;
lean_object* v___y_2405_ = stack[6].m_obj;
lean_object* v_res_2408_;
v_res_2408_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2(lean_box(0), v_ref_2400_, v_constName_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
stack->m_obj
 = v_res_2408_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2409_, lean_object* v_ref_2410_, lean_object* v_constName_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2409_, v_ref_2410_, v_constName_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v_ref_2410_);
return v_res_2417_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_2418_, lean_object* v_ref_2419_, lean_object* v_msg_2420_, lean_object* v_declHint_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_2419_, v_msg_2420_, v_declHint_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
return v___x_2427_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2419_ = stack[1].m_obj;
lean_object* v_msg_2420_ = stack[2].m_obj;
lean_object* v_declHint_2421_ = stack[3].m_obj;
lean_object* v___y_2422_ = stack[4].m_obj;
lean_object* v___y_2423_ = stack[5].m_obj;
lean_object* v___y_2424_ = stack[6].m_obj;
lean_object* v___y_2425_ = stack[7].m_obj;
lean_object* v_res_2428_;
v_res_2428_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_box(0), v_ref_2419_, v_msg_2420_, v_declHint_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
stack->m_obj
 = v_res_2428_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2429_, lean_object* v_ref_2430_, lean_object* v_msg_2431_, lean_object* v_declHint_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_00_u03b1_2429_, v_ref_2430_, v_msg_2431_, v_declHint_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v_ref_2430_);
return v_res_2438_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_2439_, lean_object* v_declHint_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_2439_, v_declHint_2440_, v___y_2444_);
return v___x_2446_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2439_ = stack[0].m_obj;
lean_object* v_declHint_2440_ = stack[1].m_obj;
lean_object* v___y_2441_ = stack[2].m_obj;
lean_object* v___y_2442_ = stack[3].m_obj;
lean_object* v___y_2443_ = stack[4].m_obj;
lean_object* v___y_2444_ = stack[5].m_obj;
lean_object* v_res_2447_;
v_res_2447_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_2439_, v_declHint_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
stack->m_obj
 = v_res_2447_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2448_, lean_object* v_declHint_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_2448_, v_declHint_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
return v_res_2455_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_2456_, lean_object* v_ref_2457_, lean_object* v_msg_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_2457_, v_msg_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
return v___x_2464_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2457_ = stack[1].m_obj;
lean_object* v_msg_2458_ = stack[2].m_obj;
lean_object* v___y_2459_ = stack[3].m_obj;
lean_object* v___y_2460_ = stack[4].m_obj;
lean_object* v___y_2461_ = stack[5].m_obj;
lean_object* v___y_2462_ = stack[6].m_obj;
lean_object* v_res_2465_;
v_res_2465_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(lean_box(0), v_ref_2457_, v_msg_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
stack->m_obj
 = v_res_2465_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2466_, lean_object* v_ref_2467_, lean_object* v_msg_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_2466_, v_ref_2467_, v_msg_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v_ref_2467_);
return v_res_2474_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_2475_, lean_object* v_msg_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v___x_2482_; 
v___x_2482_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
return v___x_2482_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2476_ = stack[1].m_obj;
lean_object* v___y_2477_ = stack[2].m_obj;
lean_object* v___y_2478_ = stack[3].m_obj;
lean_object* v___y_2479_ = stack[4].m_obj;
lean_object* v___y_2480_ = stack[5].m_obj;
lean_object* v_res_2483_;
v_res_2483_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(lean_box(0), v_msg_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
stack->m_obj
 = v_res_2483_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2484_, lean_object* v_msg_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_2484_, v_msg_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
return v_res_2491_;
}
}
uint8_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(lean_object* v_a_2492_){
_start:
{
switch(lean_obj_tag(v_a_2492_))
{
case 3:
{
uint8_t v___x_2493_; 
v___x_2493_ = 1;
return v___x_2493_;
}
case 6:
{
lean_object* v_a_2494_; 
v_a_2494_ = lean_ctor_get(v_a_2492_, 0);
v_a_2492_ = v_a_2494_;
goto _start;
}
case 4:
{
lean_object* v_f_2496_; 
v_f_2496_ = lean_ctor_get(v_a_2492_, 1);
v_a_2492_ = v_f_2496_;
goto _start;
}
case 7:
{
lean_object* v_a_2498_; 
v_a_2498_ = lean_ctor_get(v_a_2492_, 1);
v_a_2492_ = v_a_2498_;
goto _start;
}
default: 
{
uint8_t v___x_2500_; 
v___x_2500_ = 0;
return v___x_2500_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2492_ = stack[0].m_obj;
uint8_t v_res_2501_;
v_res_2501_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(v_a_2492_);
stack->m_num = v_res_2501_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat___boxed(lean_object* v_a_2502_){
_start:
{
uint8_t v_res_2503_; lean_object* v_r_2504_; 
v_res_2503_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(v_a_2502_);
lean_dec(v_a_2502_);
v_r_2504_ = lean_box(v_res_2503_);
return v_r_2504_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(lean_object* v_e_2505_, lean_object* v___y_2506_){
_start:
{
uint8_t v___x_2508_; 
v___x_2508_ = l_Lean_Expr_hasMVar(v_e_2505_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v_e_2505_);
return v___x_2509_;
}
else
{
lean_object* v___x_2510_; lean_object* v_mctx_2511_; lean_object* v___x_2512_; lean_object* v_fst_2513_; lean_object* v_snd_2514_; lean_object* v___x_2515_; lean_object* v_cache_2516_; lean_object* v_zetaDeltaFVarIds_2517_; lean_object* v_postponed_2518_; lean_object* v_diag_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2528_; 
v___x_2510_ = lean_st_ref_get(v___y_2506_);
v_mctx_2511_ = lean_ctor_get(v___x_2510_, 0);
lean_inc_ref(v_mctx_2511_);
lean_dec(v___x_2510_);
v___x_2512_ = l_Lean_instantiateMVarsCore(v_mctx_2511_, v_e_2505_);
v_fst_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_fst_2513_);
v_snd_2514_ = lean_ctor_get(v___x_2512_, 1);
lean_inc(v_snd_2514_);
lean_dec_ref(v___x_2512_);
v___x_2515_ = lean_st_ref_take(v___y_2506_);
v_cache_2516_ = lean_ctor_get(v___x_2515_, 1);
v_zetaDeltaFVarIds_2517_ = lean_ctor_get(v___x_2515_, 2);
v_postponed_2518_ = lean_ctor_get(v___x_2515_, 3);
v_diag_2519_ = lean_ctor_get(v___x_2515_, 4);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2528_ == 0)
{
lean_object* v_unused_2529_; 
v_unused_2529_ = lean_ctor_get(v___x_2515_, 0);
lean_dec(v_unused_2529_);
v___x_2521_ = v___x_2515_;
v_isShared_2522_ = v_isSharedCheck_2528_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_diag_2519_);
lean_inc(v_postponed_2518_);
lean_inc(v_zetaDeltaFVarIds_2517_);
lean_inc(v_cache_2516_);
lean_dec(v___x_2515_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2528_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 0, v_snd_2514_);
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_snd_2514_);
lean_ctor_set(v_reuseFailAlloc_2527_, 1, v_cache_2516_);
lean_ctor_set(v_reuseFailAlloc_2527_, 2, v_zetaDeltaFVarIds_2517_);
lean_ctor_set(v_reuseFailAlloc_2527_, 3, v_postponed_2518_);
lean_ctor_set(v_reuseFailAlloc_2527_, 4, v_diag_2519_);
v___x_2524_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = lean_st_ref_put(v___y_2506_, v___x_2524_);
v___x_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2526_, 0, v_fst_2513_);
return v___x_2526_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2505_ = stack[0].m_obj;
lean_object* v___y_2506_ = stack[1].m_obj;
lean_object* v_res_2530_;
v_res_2530_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_e_2505_, v___y_2506_);
stack->m_obj
 = v_res_2530_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg___boxed(lean_object* v_e_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_e_2531_, v___y_2532_);
lean_dec(v___y_2532_);
return v_res_2534_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0(lean_object* v_e_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_e_2535_, v___y_2537_);
return v___x_2541_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2535_ = stack[0].m_obj;
lean_object* v___y_2536_ = stack[1].m_obj;
lean_object* v___y_2537_ = stack[2].m_obj;
lean_object* v___y_2538_ = stack[3].m_obj;
lean_object* v___y_2539_ = stack[4].m_obj;
lean_object* v_res_2542_;
v_res_2542_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0(v_e_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
stack->m_obj
 = v_res_2542_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___boxed(lean_object* v_e_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0(v_e_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
return v_res_2549_;
}
}
lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(lean_object* v_i_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_){
_start:
{
switch(lean_obj_tag(v_i_2561_))
{
case 1:
{
lean_object* v_i_2567_; lean_object* v_expr_2568_; uint8_t v_isDisplayableTerm_2569_; lean_object* v___x_2570_; lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2691_; 
v_i_2567_ = lean_ctor_get(v_i_2561_, 0);
lean_inc_ref(v_i_2567_);
lean_dec_ref_known(v_i_2561_, 1);
v_expr_2568_ = lean_ctor_get(v_i_2567_, 3);
lean_inc_ref(v_expr_2568_);
v_isDisplayableTerm_2569_ = lean_ctor_get_uint8(v_i_2567_, sizeof(void*)*4 + 1);
lean_dec_ref(v_i_2567_);
v___x_2570_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_expr_2568_, v_a_2563_);
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2573_ = v___x_2570_;
v_isShared_2574_ = v_isSharedCheck_2691_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2570_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2691_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
uint8_t v___x_2575_; 
v___x_2575_ = l_Lean_Expr_isSort(v_a_2571_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; 
lean_del_object(v___x_2573_);
lean_inc(v_a_2565_);
lean_inc_ref(v_a_2564_);
lean_inc(v_a_2563_);
lean_inc_ref(v_a_2562_);
lean_inc(v_a_2571_);
v___x_2576_ = lean_infer_type(v_a_2571_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2578_; lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2678_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_a_2577_);
lean_dec_ref_known(v___x_2576_, 1);
v___x_2578_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_spec__0___redArg(v_a_2577_, v_a_2563_);
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2581_ = v___x_2578_;
v_isShared_2582_ = v_isSharedCheck_2678_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2678_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; 
v___x_2583_ = l_Lean_Meta_ppExpr(v_a_2579_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_);
if (lean_obj_tag(v___x_2583_) == 0)
{
if (lean_obj_tag(v_a_2571_) == 4)
{
lean_object* v_declName_2584_; lean_object* v___x_2585_; 
lean_dec_ref_known(v___x_2583_, 1);
v_declName_2584_ = lean_ctor_get(v_a_2571_, 0);
lean_inc_n(v_declName_2584_, 2);
lean_dec_ref_known(v_a_2571_, 2);
v___x_2585_ = l_Lean_PrettyPrinter_ppSignature(v_declName_2584_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_a_2586_; lean_object* v___x_2587_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_a_2586_);
lean_dec_ref_known(v___x_2585_, 1);
v___x_2587_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f(v_declName_2584_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2612_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2612_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2612_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v_fmt_2592_; lean_object* v_infos_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2611_; 
v_fmt_2592_ = lean_ctor_get(v_a_2586_, 0);
v_infos_2593_ = lean_ctor_get(v_a_2586_, 1);
v_isSharedCheck_2611_ = !lean_is_exclusive(v_a_2586_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2595_ = v_a_2586_;
v_isShared_2596_ = v_isSharedCheck_2611_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_infos_2593_);
lean_inc(v_fmt_2592_);
lean_dec(v_a_2586_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2611_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2602_; 
v___x_2597_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1));
v___x_2598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2597_);
lean_ctor_set(v___x_2598_, 1, v_fmt_2592_);
v___x_2599_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3));
v___x_2600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2598_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2600_);
v___x_2602_ = v___x_2595_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2600_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_infos_2593_);
v___x_2602_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2604_; 
if (v_isShared_2582_ == 0)
{
lean_ctor_set_tag(v___x_2581_, 1);
lean_ctor_set(v___x_2581_, 0, v___x_2602_);
v___x_2604_ = v___x_2581_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2602_);
v___x_2604_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
lean_object* v___x_2605_; lean_object* v___x_2607_; 
v___x_2605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2604_);
lean_ctor_set(v___x_2605_, 1, v_a_2588_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v___x_2605_);
v___x_2607_ = v___x_2590_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec(v_a_2586_);
lean_del_object(v___x_2581_);
v_a_2613_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2587_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2587_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec(v_declName_2584_);
lean_del_object(v___x_2581_);
v_a_2621_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2585_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2585_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2630_; 
v_a_2629_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_a_2629_);
lean_dec_ref_known(v___x_2583_, 1);
lean_inc(v_a_2571_);
v___x_2630_ = l_Lean_Meta_ppExpr(v_a_2571_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2661_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2633_ = v___x_2630_;
v_isShared_2634_ = v_isSharedCheck_2661_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2630_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2661_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___y_2636_; 
if (v_isDisplayableTerm_2569_ == 0)
{
if (lean_obj_tag(v_a_2571_) == 1)
{
lean_object* v_lctx_2655_; lean_object* v___x_2656_; 
v_lctx_2655_ = lean_ctor_get(v_a_2562_, 2);
lean_inc_ref(v_lctx_2655_);
v___x_2656_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_2655_, v_a_2571_);
lean_dec_ref_known(v_a_2571_, 1);
if (lean_obj_tag(v___x_2656_) == 1)
{
lean_object* v_val_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; 
v_val_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_val_2657_);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2658_ = l_Lean_LocalDecl_userName(v_val_2657_);
lean_dec(v_val_2657_);
v___x_2659_ = l_Lean_Name_hasMacroScopes(v___x_2658_);
lean_dec(v___x_2658_);
if (v___x_2659_ == 0)
{
goto v___jp_2651_;
}
else
{
lean_dec(v_a_2631_);
v___y_2636_ = v_a_2629_;
goto v___jp_2635_;
}
}
else
{
lean_dec(v___x_2656_);
lean_dec(v_a_2631_);
v___y_2636_ = v_a_2629_;
goto v___jp_2635_;
}
}
else
{
uint8_t v___x_2660_; 
lean_dec(v_a_2571_);
v___x_2660_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_isAtomicFormat(v_a_2631_);
if (v___x_2660_ == 0)
{
lean_dec(v_a_2631_);
v___y_2636_ = v_a_2629_;
goto v___jp_2635_;
}
else
{
goto v___jp_2651_;
}
}
}
else
{
lean_dec(v_a_2571_);
goto v___jp_2651_;
}
v___jp_2635_:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2644_; 
v___x_2637_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1));
v___x_2638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2637_);
lean_ctor_set(v___x_2638_, 1, v___y_2636_);
v___x_2639_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3));
v___x_2640_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2638_);
lean_ctor_set(v___x_2640_, 1, v___x_2639_);
v___x_2641_ = lean_box(1);
v___x_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2640_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set_tag(v___x_2581_, 1);
lean_ctor_set(v___x_2581_, 0, v___x_2642_);
v___x_2644_ = v___x_2581_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2642_);
v___x_2644_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2648_; 
v___x_2645_ = lean_box(0);
v___x_2646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2644_);
lean_ctor_set(v___x_2646_, 1, v___x_2645_);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 0, v___x_2646_);
v___x_2648_ = v___x_2633_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
v___jp_2651_:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2652_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5));
v___x_2653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2653_, 0, v_a_2631_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
v___x_2654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
lean_ctor_set(v___x_2654_, 1, v_a_2629_);
v___y_2636_ = v___x_2654_;
goto v___jp_2635_;
}
}
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
lean_dec(v_a_2629_);
lean_del_object(v___x_2581_);
lean_dec(v_a_2571_);
v_a_2662_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2630_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2630_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
lean_del_object(v___x_2581_);
lean_dec(v_a_2571_);
v_a_2670_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2583_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2583_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
lean_dec(v_a_2571_);
v_a_2679_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2576_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2576_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
else
{
lean_object* v___x_2687_; lean_object* v___x_2689_; 
lean_dec(v_a_2571_);
v___x_2687_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6));
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2687_);
v___x_2689_ = v___x_2573_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2687_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
case 7:
{
lean_object* v_i_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2742_; 
v_i_2692_ = lean_ctor_get(v_i_2561_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_i_2561_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2694_ = v_i_2561_;
v_isShared_2695_ = v_isSharedCheck_2742_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_i_2692_);
lean_dec(v_i_2561_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2742_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v_fieldName_2696_; lean_object* v_val_2697_; lean_object* v___x_2698_; 
v_fieldName_2696_ = lean_ctor_get(v_i_2692_, 1);
lean_inc(v_fieldName_2696_);
v_val_2697_ = lean_ctor_get(v_i_2692_, 3);
lean_inc_ref(v_val_2697_);
lean_dec_ref(v_i_2692_);
lean_inc(v_a_2565_);
lean_inc_ref(v_a_2564_);
lean_inc(v_a_2563_);
lean_inc_ref(v_a_2562_);
v___x_2698_ = lean_infer_type(v_val_2697_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; lean_object* v___x_2700_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2698_, 1);
v___x_2700_ = l_Lean_Meta_ppExpr(v_a_2699_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2725_; 
v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2703_ = v___x_2700_;
v_isShared_2704_ = v_isSharedCheck_2725_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2700_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2725_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2705_; uint8_t v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2709_; 
v___x_2705_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__1));
v___x_2706_ = 1;
v___x_2707_ = l_Lean_Name_toString(v_fieldName_2696_, v___x_2706_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set_tag(v___x_2694_, 3);
lean_ctor_set(v___x_2694_, 0, v___x_2707_);
v___x_2709_ = v___x_2694_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2707_);
v___x_2709_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2722_; 
v___x_2710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2705_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__5));
v___x_2712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2710_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___x_2713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
lean_ctor_set(v___x_2713_, 1, v_a_2701_);
v___x_2714_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__3));
v___x_2715_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2713_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = lean_box(1);
v___x_2717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2715_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
v___x_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
v___x_2719_ = lean_box(0);
v___x_2720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2718_);
lean_ctor_set(v___x_2720_, 1, v___x_2719_);
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 0, v___x_2720_);
v___x_2722_ = v___x_2703_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_dec(v_fieldName_2696_);
lean_del_object(v___x_2694_);
v_a_2726_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___x_2700_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2700_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec(v_fieldName_2696_);
lean_del_object(v___x_2694_);
v_a_2734_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2698_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2698_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
}
default: 
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
lean_dec_ref(v_i_2561_);
v___x_2743_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___closed__6));
v___x_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
return v___x_2744_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_2561_ = stack[0].m_obj;
lean_object* v_a_2562_ = stack[1].m_obj;
lean_object* v_a_2563_ = stack[2].m_obj;
lean_object* v_a_2564_ = stack[3].m_obj;
lean_object* v_a_2565_ = stack[4].m_obj;
lean_object* v_res_2745_;
v_res_2745_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(v_i_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_);
stack->m_obj
 = v_res_2745_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f___boxed(lean_object* v_i_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(v_i_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
return v_res_2752_;
}
}
lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__0(lean_object* v_snd_2753_, lean_object* v_____r_2754_, lean_object* v_fmts_2755_, lean_object* v_infos_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2762_, 0, v_fmts_2755_);
lean_ctor_set(v___x_2762_, 1, v_infos_2756_);
v___x_2763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2763_, 0, v_snd_2753_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2763_);
return v___x_2764_;
}
}
LEAN_EXPORT void l_Lean_Elab_Info_fmtHover_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_2753_ = stack[0].m_obj;
lean_object* v_____r_2754_ = stack[1].m_obj;
lean_object* v_fmts_2755_ = stack[2].m_obj;
lean_object* v_infos_2756_ = stack[3].m_obj;
lean_object* v___y_2757_ = stack[4].m_obj;
lean_object* v___y_2758_ = stack[5].m_obj;
lean_object* v___y_2759_ = stack[6].m_obj;
lean_object* v___y_2760_ = stack[7].m_obj;
lean_object* v_res_2765_;
v_res_2765_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(v_snd_2753_, v_____r_2754_, v_fmts_2755_, v_infos_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
stack->m_obj
 = v_res_2765_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__0___boxed(lean_object* v_snd_2766_, lean_object* v_____r_2767_, lean_object* v_fmts_2768_, lean_object* v_infos_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(v_snd_2766_, v_____r_2767_, v_fmts_2768_, v_infos_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0_spec__0(lean_object* v_x_2776_, lean_object* v_x_2777_, lean_object* v_x_2778_){
_start:
{
if (lean_obj_tag(v_x_2778_) == 0)
{
lean_dec(v_x_2776_);
return v_x_2777_;
}
else
{
lean_object* v_head_2779_; lean_object* v_tail_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2789_; 
v_head_2779_ = lean_ctor_get(v_x_2778_, 0);
v_tail_2780_ = lean_ctor_get(v_x_2778_, 1);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_x_2778_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2782_ = v_x_2778_;
v_isShared_2783_ = v_isSharedCheck_2789_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_tail_2780_);
lean_inc(v_head_2779_);
lean_dec(v_x_2778_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2789_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
lean_inc(v_x_2776_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set_tag(v___x_2782_, 5);
lean_ctor_set(v___x_2782_, 1, v_x_2776_);
lean_ctor_set(v___x_2782_, 0, v_x_2777_);
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_x_2777_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v_x_2776_);
v___x_2785_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
lean_object* v___x_2786_; 
v___x_2786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
lean_ctor_set(v___x_2786_, 1, v_head_2779_);
v_x_2777_ = v___x_2786_;
v_x_2778_ = v_tail_2780_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0(lean_object* v_x_2790_, lean_object* v_x_2791_){
_start:
{
if (lean_obj_tag(v_x_2790_) == 0)
{
lean_object* v___x_2792_; 
lean_dec(v_x_2791_);
v___x_2792_ = lean_box(0);
return v___x_2792_;
}
else
{
lean_object* v_tail_2793_; 
v_tail_2793_ = lean_ctor_get(v_x_2790_, 1);
if (lean_obj_tag(v_tail_2793_) == 0)
{
lean_object* v_head_2794_; 
lean_dec(v_x_2791_);
v_head_2794_ = lean_ctor_get(v_x_2790_, 0);
lean_inc(v_head_2794_);
lean_dec_ref_known(v_x_2790_, 2);
return v_head_2794_;
}
else
{
lean_object* v_head_2795_; lean_object* v___x_2796_; 
lean_inc(v_tail_2793_);
v_head_2795_ = lean_ctor_get(v_x_2790_, 0);
lean_inc(v_head_2795_);
lean_dec_ref_known(v_x_2790_, 2);
v___x_2796_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0_spec__0(v_x_2791_, v_head_2795_, v_tail_2793_);
return v___x_2796_;
}
}
}
}
lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__1(lean_object* v___x_2800_, lean_object* v_i_2801_, lean_object* v_fmts_2802_, lean_object* v_infos_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v___y_2810_; lean_object* v_fmts_2811_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v_fmts_2825_; lean_object* v_fst_2829_; lean_object* v_fst_2830_; lean_object* v_snd_2831_; lean_object* v___y_2852_; uint8_t v___y_2853_; lean_object* v_a_2857_; lean_object* v___y_2861_; lean_object* v___x_2867_; 
lean_inc_ref(v_i_2801_);
v___x_2867_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_Info_fmtHover_x3f_fmtTermAndModule_x3f(v_i_2801_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v_fst_2869_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2868_);
lean_dec_ref_known(v___x_2867_, 1);
v_fst_2869_ = lean_ctor_get(v_a_2868_, 0);
if (lean_obj_tag(v_fst_2869_) == 1)
{
lean_object* v_val_2870_; lean_object* v_snd_2871_; lean_object* v_fmt_2872_; lean_object* v_infos_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
lean_dec(v_infos_2803_);
v_val_2870_ = lean_ctor_get(v_fst_2869_, 0);
lean_inc(v_val_2870_);
v_snd_2871_ = lean_ctor_get(v_a_2868_, 1);
lean_inc(v_snd_2871_);
lean_dec(v_a_2868_);
v_fmt_2872_ = lean_ctor_get(v_val_2870_, 0);
lean_inc(v_fmt_2872_);
v_infos_2873_ = lean_ctor_get(v_val_2870_, 1);
lean_inc(v_infos_2873_);
lean_dec(v_val_2870_);
v___x_2874_ = lean_array_push(v_fmts_2802_, v_fmt_2872_);
v___x_2875_ = lean_box(0);
v___x_2876_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(v_snd_2871_, v___x_2875_, v___x_2874_, v_infos_2873_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
v___y_2861_ = v___x_2876_;
goto v___jp_2860_;
}
else
{
lean_object* v_snd_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_snd_2877_ = lean_ctor_get(v_a_2868_, 1);
lean_inc(v_snd_2877_);
lean_dec(v_a_2868_);
v___x_2878_ = lean_box(0);
v___x_2879_ = l_Lean_Elab_Info_fmtHover_x3f___lam__0(v_snd_2877_, v___x_2878_, v_fmts_2802_, v_infos_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
v___y_2861_ = v___x_2879_;
goto v___jp_2860_;
}
}
else
{
lean_object* v_a_2880_; 
v_a_2880_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2880_);
lean_dec_ref_known(v___x_2867_, 1);
v_a_2857_ = v_a_2880_;
goto v___jp_2856_;
}
v___jp_2809_:
{
lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2812_ = lean_array_get_size(v_fmts_2811_);
v___x_2813_ = lean_nat_dec_eq(v___x_2812_, v___x_2800_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2814_ = lean_array_to_list(v_fmts_2811_);
v___x_2815_ = ((lean_object*)(l_Lean_Elab_Info_fmtHover_x3f___lam__1___closed__1));
v___x_2816_ = l_Std_Format_joinSep___at___00Lean_Elab_Info_fmtHover_x3f_spec__0(v___x_2814_, v___x_2815_);
v___x_2817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2816_);
lean_ctor_set(v___x_2817_, 1, v___y_2810_);
v___x_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
v___x_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2818_);
return v___x_2819_;
}
else
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
lean_dec_ref(v_fmts_2811_);
lean_dec(v___y_2810_);
v___x_2820_ = lean_box(0);
v___x_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2820_);
return v___x_2821_;
}
}
v___jp_2822_:
{
if (lean_obj_tag(v___y_2824_) == 1)
{
lean_object* v_val_2826_; lean_object* v___x_2827_; 
v_val_2826_ = lean_ctor_get(v___y_2824_, 0);
lean_inc(v_val_2826_);
lean_dec_ref_known(v___y_2824_, 1);
v___x_2827_ = lean_array_push(v_fmts_2825_, v_val_2826_);
v___y_2810_ = v___y_2823_;
v_fmts_2811_ = v___x_2827_;
goto v___jp_2809_;
}
else
{
lean_dec(v___y_2824_);
v___y_2810_ = v___y_2823_;
v_fmts_2811_ = v_fmts_2825_;
goto v___jp_2809_;
}
}
v___jp_2828_:
{
lean_object* v___x_2832_; 
v___x_2832_ = l_Lean_Elab_Info_docString_x3f(v_i_2801_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; 
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2833_);
lean_dec_ref_known(v___x_2832_, 1);
if (lean_obj_tag(v_a_2833_) == 1)
{
lean_object* v_val_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2842_; 
v_val_2834_ = lean_ctor_get(v_a_2833_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_a_2833_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2836_ = v_a_2833_;
v_isShared_2837_ = v_isSharedCheck_2842_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_val_2834_);
lean_dec(v_a_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2842_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set_tag(v___x_2836_, 3);
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_val_2834_);
v___x_2839_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
lean_object* v___x_2840_; 
v___x_2840_ = lean_array_push(v_fst_2830_, v___x_2839_);
v___y_2823_ = v_snd_2831_;
v___y_2824_ = v_fst_2829_;
v_fmts_2825_ = v___x_2840_;
goto v___jp_2822_;
}
}
}
else
{
lean_dec(v_a_2833_);
v___y_2823_ = v_snd_2831_;
v___y_2824_ = v_fst_2829_;
v_fmts_2825_ = v_fst_2830_;
goto v___jp_2822_;
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_dec(v_snd_2831_);
lean_dec(v_fst_2830_);
lean_dec(v_fst_2829_);
v_a_2843_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2832_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2832_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
v___jp_2851_:
{
if (v___y_2853_ == 0)
{
lean_object* v___x_2854_; 
lean_dec_ref(v___y_2852_);
v___x_2854_ = lean_box(0);
v_fst_2829_ = v___x_2854_;
v_fst_2830_ = v_fmts_2802_;
v_snd_2831_ = v_infos_2803_;
goto v___jp_2828_;
}
else
{
lean_object* v___x_2855_; 
lean_dec(v_infos_2803_);
lean_dec_ref(v_fmts_2802_);
lean_dec_ref(v_i_2801_);
v___x_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2855_, 0, v___y_2852_);
return v___x_2855_;
}
}
v___jp_2856_:
{
uint8_t v___x_2858_; 
v___x_2858_ = l_Lean_Exception_isInterrupt(v_a_2857_);
if (v___x_2858_ == 0)
{
uint8_t v___x_2859_; 
lean_inc_ref(v_a_2857_);
v___x_2859_ = l_Lean_Exception_isRuntime(v_a_2857_);
v___y_2852_ = v_a_2857_;
v___y_2853_ = v___x_2859_;
goto v___jp_2851_;
}
else
{
v___y_2852_ = v_a_2857_;
v___y_2853_ = v___x_2858_;
goto v___jp_2851_;
}
}
v___jp_2860_:
{
lean_object* v_a_2862_; lean_object* v_snd_2863_; lean_object* v_fst_2864_; lean_object* v_fst_2865_; lean_object* v_snd_2866_; 
v_a_2862_ = lean_ctor_get(v___y_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref(v___y_2861_);
v_snd_2863_ = lean_ctor_get(v_a_2862_, 1);
lean_inc(v_snd_2863_);
v_fst_2864_ = lean_ctor_get(v_a_2862_, 0);
lean_inc(v_fst_2864_);
lean_dec(v_a_2862_);
v_fst_2865_ = lean_ctor_get(v_snd_2863_, 0);
lean_inc(v_fst_2865_);
v_snd_2866_ = lean_ctor_get(v_snd_2863_, 1);
lean_inc(v_snd_2866_);
lean_dec(v_snd_2863_);
v_fst_2829_ = v_fst_2864_;
v_fst_2830_ = v_fst_2865_;
v_snd_2831_ = v_snd_2866_;
goto v___jp_2828_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Info_fmtHover_x3f___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2800_ = stack[0].m_obj;
lean_object* v_i_2801_ = stack[1].m_obj;
lean_object* v_fmts_2802_ = stack[2].m_obj;
lean_object* v_infos_2803_ = stack[3].m_obj;
lean_object* v___y_2804_ = stack[4].m_obj;
lean_object* v___y_2805_ = stack[5].m_obj;
lean_object* v___y_2806_ = stack[6].m_obj;
lean_object* v___y_2807_ = stack[7].m_obj;
lean_object* v_res_2881_;
v_res_2881_ = l_Lean_Elab_Info_fmtHover_x3f___lam__1(v___x_2800_, v_i_2801_, v_fmts_2802_, v_infos_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
stack->m_obj
 = v_res_2881_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___lam__1___boxed(lean_object* v___x_2882_, lean_object* v_i_2883_, lean_object* v_fmts_2884_, lean_object* v_infos_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l_Lean_Elab_Info_fmtHover_x3f___lam__1(v___x_2882_, v_i_2883_, v_fmts_2884_, v_infos_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___x_2882_);
return v_res_2891_;
}
}
lean_object* l_Lean_Elab_Info_fmtHover_x3f(lean_object* v_ci_2894_, lean_object* v_i_2895_){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v_fmts_2899_; lean_object* v_infos_2900_; lean_object* v___f_2901_; lean_object* v___x_2902_; 
v___x_2897_ = l_Lean_Elab_Info_lctx(v_i_2895_);
v___x_2898_ = lean_unsigned_to_nat(0u);
v_fmts_2899_ = ((lean_object*)(l_Lean_Elab_Info_fmtHover_x3f___closed__0));
v_infos_2900_ = lean_box(1);
v___f_2901_ = lean_alloc_closure((void*)(l_Lean_Elab_Info_fmtHover_x3f___lam__1___boxed), 9, 4);
lean_closure_set(v___f_2901_, 0, v___x_2898_);
lean_closure_set(v___f_2901_, 1, v_i_2895_);
lean_closure_set(v___f_2901_, 2, v_fmts_2899_);
lean_closure_set(v___f_2901_, 3, v_infos_2900_);
v___x_2902_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ci_2894_, v___x_2897_, v___f_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT void l_Lean_Elab_Info_fmtHover_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_ci_2894_ = stack[0].m_obj;
lean_object* v_i_2895_ = stack[1].m_obj;
lean_object* v_res_2903_;
v_res_2903_ = l_Lean_Elab_Info_fmtHover_x3f(v_ci_2894_, v_i_2895_);
stack->m_obj
 = v_res_2903_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_fmtHover_x3f___boxed(lean_object* v_ci_2904_, lean_object* v_i_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Lean_Elab_Info_fmtHover_x3f(v_ci_2904_, v_i_2905_);
return v_res_2907_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(lean_object* v_hoverPos_2916_, lean_object* v_pos_2917_, lean_object* v_tailPos_2918_, lean_object* v_as_2919_, size_t v_i_2920_, size_t v_stop_2921_){
_start:
{
uint8_t v___x_2922_; 
v___x_2922_ = lean_usize_dec_eq(v_i_2920_, v_stop_2921_);
if (v___x_2922_ == 0)
{
lean_object* v___x_2923_; uint8_t v___x_2924_; 
v___x_2923_ = lean_array_uget_borrowed(v_as_2919_, v_i_2920_);
v___x_2924_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(v_hoverPos_2916_, v_pos_2917_, v_tailPos_2918_, v___x_2923_);
if (v___x_2924_ == 0)
{
size_t v___x_2925_; size_t v___x_2926_; 
v___x_2925_ = ((size_t)1ULL);
v___x_2926_ = lean_usize_add(v_i_2920_, v___x_2925_);
v_i_2920_ = v___x_2926_;
goto _start;
}
else
{
return v___x_2924_;
}
}
else
{
uint8_t v___x_2928_; 
v___x_2928_ = 0;
return v___x_2928_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_hoverPos_2916_ = stack[0].m_obj;
lean_object* v_pos_2917_ = stack[1].m_obj;
lean_object* v_tailPos_2918_ = stack[2].m_obj;
lean_object* v_as_2919_ = stack[3].m_obj;
size_t v_i_2920_ = stack[4].m_num;
size_t v_stop_2921_ = stack[5].m_num;
uint8_t v_res_2929_;
v_res_2929_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(v_hoverPos_2916_, v_pos_2917_, v_tailPos_2918_, v_as_2919_, v_i_2920_, v_stop_2921_);
stack->m_num = v_res_2929_;
}
uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(lean_object* v_hoverPos_2930_, lean_object* v_pos_2931_, lean_object* v_tailPos_2932_, lean_object* v_x_2933_){
_start:
{
if (lean_obj_tag(v_x_2933_) == 0)
{
lean_object* v_cs_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; uint8_t v___x_2937_; 
v_cs_2934_ = lean_ctor_get(v_x_2933_, 0);
v___x_2935_ = lean_unsigned_to_nat(0u);
v___x_2936_ = lean_array_get_size(v_cs_2934_);
v___x_2937_ = lean_nat_dec_lt(v___x_2935_, v___x_2936_);
if (v___x_2937_ == 0)
{
return v___x_2937_;
}
else
{
if (v___x_2937_ == 0)
{
return v___x_2937_;
}
else
{
size_t v___x_2938_; size_t v___x_2939_; uint8_t v___x_2940_; 
v___x_2938_ = ((size_t)0ULL);
v___x_2939_ = lean_usize_of_nat(v___x_2936_);
v___x_2940_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(v_hoverPos_2930_, v_pos_2931_, v_tailPos_2932_, v_cs_2934_, v___x_2938_, v___x_2939_);
return v___x_2940_;
}
}
}
else
{
lean_object* v_vs_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; uint8_t v___x_2944_; 
v_vs_2941_ = lean_ctor_get(v_x_2933_, 0);
v___x_2942_ = lean_unsigned_to_nat(0u);
v___x_2943_ = lean_array_get_size(v_vs_2941_);
v___x_2944_ = lean_nat_dec_lt(v___x_2942_, v___x_2943_);
if (v___x_2944_ == 0)
{
return v___x_2944_;
}
else
{
if (v___x_2944_ == 0)
{
return v___x_2944_;
}
else
{
size_t v___x_2945_; size_t v___x_2946_; uint8_t v___x_2947_; 
v___x_2945_ = ((size_t)0ULL);
v___x_2946_ = lean_usize_of_nat(v___x_2943_);
v___x_2947_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_2930_, v_pos_2931_, v_tailPos_2932_, v_vs_2941_, v___x_2945_, v___x_2946_);
return v___x_2947_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_hoverPos_2930_ = stack[0].m_obj;
lean_object* v_pos_2931_ = stack[1].m_obj;
lean_object* v_tailPos_2932_ = stack[2].m_obj;
lean_object* v_x_2933_ = stack[3].m_obj;
uint8_t v_res_2948_;
v_res_2948_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(v_hoverPos_2930_, v_pos_2931_, v_tailPos_2932_, v_x_2933_);
stack->m_num = v_res_2948_;
}
uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(lean_object* v_hoverPos_2949_, lean_object* v_pos_2950_, lean_object* v_tailPos_2951_, lean_object* v_t_2952_){
_start:
{
lean_object* v_root_2953_; lean_object* v_tail_2954_; uint8_t v___x_2955_; 
v_root_2953_ = lean_ctor_get(v_t_2952_, 0);
v_tail_2954_ = lean_ctor_get(v_t_2952_, 1);
v___x_2955_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(v_hoverPos_2949_, v_pos_2950_, v_tailPos_2951_, v_root_2953_);
if (v___x_2955_ == 0)
{
lean_object* v___x_2956_; lean_object* v___x_2957_; uint8_t v___x_2958_; 
v___x_2956_ = lean_unsigned_to_nat(0u);
v___x_2957_ = lean_array_get_size(v_tail_2954_);
v___x_2958_ = lean_nat_dec_lt(v___x_2956_, v___x_2957_);
if (v___x_2958_ == 0)
{
return v___x_2958_;
}
else
{
if (v___x_2958_ == 0)
{
return v___x_2958_;
}
else
{
size_t v___x_2959_; size_t v___x_2960_; uint8_t v___x_2961_; 
v___x_2959_ = ((size_t)0ULL);
v___x_2960_ = lean_usize_of_nat(v___x_2957_);
v___x_2961_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_2949_, v_pos_2950_, v_tailPos_2951_, v_tail_2954_, v___x_2959_, v___x_2960_);
return v___x_2961_;
}
}
}
else
{
return v___x_2955_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_hoverPos_2949_ = stack[0].m_obj;
lean_object* v_pos_2950_ = stack[1].m_obj;
lean_object* v_tailPos_2951_ = stack[2].m_obj;
lean_object* v_t_2952_ = stack[3].m_obj;
uint8_t v_res_2962_;
v_res_2962_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2949_, v_pos_2950_, v_tailPos_2951_, v_t_2952_);
stack->m_num = v_res_2962_;
}
uint8_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(lean_object* v_hoverPos_2963_, lean_object* v_pos_2964_, lean_object* v_tailPos_2965_, lean_object* v_a_2966_){
_start:
{
if (lean_obj_tag(v_a_2966_) == 1)
{
lean_object* v_i_2967_; 
v_i_2967_ = lean_ctor_get(v_a_2966_, 0);
switch(lean_obj_tag(v_i_2967_))
{
case 0:
{
lean_object* v_children_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; uint8_t v___x_2971_; 
v_children_2968_ = lean_ctor_get(v_a_2966_, 1);
v___x_2969_ = l_Lean_Elab_Info_stx(v_i_2967_);
v___x_2970_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___closed__3));
v___x_2971_ = l_Lean_Syntax_isOfKind(v___x_2969_, v___x_2970_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Lean_Elab_Info_pos_x3f(v_i_2967_);
if (lean_obj_tag(v___x_2972_) == 1)
{
lean_object* v_val_2973_; lean_object* v___x_2974_; 
v_val_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_val_2973_);
lean_dec_ref_known(v___x_2972_, 1);
v___x_2974_ = l_Lean_Elab_Info_tailPos_x3f(v_i_2967_);
if (lean_obj_tag(v___x_2974_) == 1)
{
lean_object* v_val_2975_; uint8_t v___x_2976_; uint8_t v___y_2978_; lean_object* v___x_2980_; lean_object* v___x_2981_; uint8_t v___x_2982_; 
v_val_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_val_2975_);
lean_dec_ref_known(v___x_2974_, 1);
v___x_2976_ = 1;
v___x_2980_ = lean_unsigned_to_nat(1u);
v___x_2981_ = lean_nat_add(v_hoverPos_2963_, v___x_2980_);
v___x_2982_ = lean_nat_dec_le(v___x_2981_, v_val_2975_);
lean_dec(v___x_2981_);
if (v___x_2982_ == 0)
{
lean_dec(v_val_2975_);
lean_dec(v_val_2973_);
v___y_2978_ = v___x_2971_;
goto v___jp_2977_;
}
else
{
uint8_t v_decide_2983_; 
v_decide_2983_ = lean_nat_dec_eq(v_val_2973_, v_pos_2964_);
lean_dec(v_val_2973_);
if (v_decide_2983_ == 0)
{
lean_dec(v_val_2975_);
v___y_2978_ = v___x_2982_;
goto v___jp_2977_;
}
else
{
uint8_t v_decide_2984_; 
v_decide_2984_ = lean_nat_dec_eq(v_val_2975_, v_tailPos_2965_);
lean_dec(v_val_2975_);
if (v_decide_2984_ == 0)
{
v___y_2978_ = v___x_2982_;
goto v___jp_2977_;
}
else
{
v___y_2978_ = v___x_2971_;
goto v___jp_2977_;
}
}
}
v___jp_2977_:
{
if (v___y_2978_ == 0)
{
uint8_t v___x_2979_; 
v___x_2979_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2963_, v_pos_2964_, v_tailPos_2965_, v_children_2968_);
return v___x_2979_;
}
else
{
return v___x_2976_;
}
}
}
else
{
uint8_t v___x_2985_; 
lean_dec(v___x_2974_);
lean_dec(v_val_2973_);
v___x_2985_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2963_, v_pos_2964_, v_tailPos_2965_, v_children_2968_);
return v___x_2985_;
}
}
else
{
uint8_t v___x_2986_; 
lean_dec(v___x_2972_);
v___x_2986_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2963_, v_pos_2964_, v_tailPos_2965_, v_children_2968_);
return v___x_2986_;
}
}
else
{
uint8_t v___x_2987_; 
v___x_2987_ = 0;
return v___x_2987_;
}
}
case 4:
{
lean_object* v_children_2988_; uint8_t v___x_2989_; 
v_children_2988_ = lean_ctor_get(v_a_2966_, 1);
v___x_2989_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_2963_, v_pos_2964_, v_tailPos_2965_, v_children_2988_);
return v___x_2989_;
}
default: 
{
uint8_t v___x_2990_; 
v___x_2990_ = 0;
return v___x_2990_;
}
}
}
else
{
uint8_t v___x_2991_; 
v___x_2991_ = 0;
return v___x_2991_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_0interp(lean_interpreter_value* stack)
{
lean_object* v_hoverPos_2963_ = stack[0].m_obj;
lean_object* v_pos_2964_ = stack[1].m_obj;
lean_object* v_tailPos_2965_ = stack[2].m_obj;
lean_object* v_a_2966_ = stack[3].m_obj;
uint8_t v_res_2992_;
v_res_2992_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(v_hoverPos_2963_, v_pos_2964_, v_tailPos_2965_, v_a_2966_);
stack->m_num = v_res_2992_;
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(lean_object* v_hoverPos_2993_, lean_object* v_pos_2994_, lean_object* v_tailPos_2995_, lean_object* v_as_2996_, size_t v_i_2997_, size_t v_stop_2998_){
_start:
{
uint8_t v___x_2999_; 
v___x_2999_ = lean_usize_dec_eq(v_i_2997_, v_stop_2998_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3000_; uint8_t v___x_3001_; 
v___x_3000_ = lean_array_uget_borrowed(v_as_2996_, v_i_2997_);
v___x_3001_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(v_hoverPos_2993_, v_pos_2994_, v_tailPos_2995_, v___x_3000_);
if (v___x_3001_ == 0)
{
size_t v___x_3002_; size_t v___x_3003_; 
v___x_3002_ = ((size_t)1ULL);
v___x_3003_ = lean_usize_add(v_i_2997_, v___x_3002_);
v_i_2997_ = v___x_3003_;
goto _start;
}
else
{
return v___x_3001_;
}
}
else
{
uint8_t v___x_3005_; 
v___x_3005_ = 0;
return v___x_3005_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_hoverPos_2993_ = stack[0].m_obj;
lean_object* v_pos_2994_ = stack[1].m_obj;
lean_object* v_tailPos_2995_ = stack[2].m_obj;
lean_object* v_as_2996_ = stack[3].m_obj;
size_t v_i_2997_ = stack[4].m_num;
size_t v_stop_2998_ = stack[5].m_num;
uint8_t v_res_3006_;
v_res_3006_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_2993_, v_pos_2994_, v_tailPos_2995_, v_as_2996_, v_i_2997_, v_stop_2998_);
stack->m_num = v_res_3006_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1___boxed(lean_object* v_hoverPos_3007_, lean_object* v_pos_3008_, lean_object* v_tailPos_3009_, lean_object* v_as_3010_, lean_object* v_i_3011_, lean_object* v_stop_3012_){
_start:
{
size_t v_i_boxed_3013_; size_t v_stop_boxed_3014_; uint8_t v_res_3015_; lean_object* v_r_3016_; 
v_i_boxed_3013_ = lean_unbox_usize(v_i_3011_);
lean_dec(v_i_3011_);
v_stop_boxed_3014_ = lean_unbox_usize(v_stop_3012_);
lean_dec(v_stop_3012_);
v_res_3015_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__1(v_hoverPos_3007_, v_pos_3008_, v_tailPos_3009_, v_as_3010_, v_i_boxed_3013_, v_stop_boxed_3014_);
lean_dec_ref(v_as_3010_);
lean_dec(v_tailPos_3009_);
lean_dec(v_pos_3008_);
lean_dec(v_hoverPos_3007_);
v_r_3016_ = lean_box(v_res_3015_);
return v_r_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1___boxed(lean_object* v_hoverPos_3017_, lean_object* v_pos_3018_, lean_object* v_tailPos_3019_, lean_object* v_as_3020_, lean_object* v_i_3021_, lean_object* v_stop_3022_){
_start:
{
size_t v_i_boxed_3023_; size_t v_stop_boxed_3024_; uint8_t v_res_3025_; lean_object* v_r_3026_; 
v_i_boxed_3023_ = lean_unbox_usize(v_i_3021_);
lean_dec(v_i_3021_);
v_stop_boxed_3024_ = lean_unbox_usize(v_stop_3022_);
lean_dec(v_stop_3022_);
v_res_3025_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0_spec__1(v_hoverPos_3017_, v_pos_3018_, v_tailPos_3019_, v_as_3020_, v_i_boxed_3023_, v_stop_boxed_3024_);
lean_dec_ref(v_as_3020_);
lean_dec(v_tailPos_3019_);
lean_dec(v_pos_3018_);
lean_dec(v_hoverPos_3017_);
v_r_3026_ = lean_box(v_res_3025_);
return v_r_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0___boxed(lean_object* v_hoverPos_3027_, lean_object* v_pos_3028_, lean_object* v_tailPos_3029_, lean_object* v_t_3030_){
_start:
{
uint8_t v_res_3031_; lean_object* v_r_3032_; 
v_res_3031_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_3027_, v_pos_3028_, v_tailPos_3029_, v_t_3030_);
lean_dec_ref(v_t_3030_);
lean_dec(v_tailPos_3029_);
lean_dec(v_pos_3028_);
lean_dec(v_hoverPos_3027_);
v_r_3032_ = lean_box(v_res_3031_);
return v_r_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0___boxed(lean_object* v_hoverPos_3033_, lean_object* v_pos_3034_, lean_object* v_tailPos_3035_, lean_object* v_x_3036_){
_start:
{
uint8_t v_res_3037_; lean_object* v_r_3038_; 
v_res_3037_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0_spec__0(v_hoverPos_3033_, v_pos_3034_, v_tailPos_3035_, v_x_3036_);
lean_dec_ref(v_x_3036_);
lean_dec(v_tailPos_3035_);
lean_dec(v_pos_3034_);
lean_dec(v_hoverPos_3033_);
v_r_3038_ = lean_box(v_res_3037_);
return v_r_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic___boxed(lean_object* v_hoverPos_3039_, lean_object* v_pos_3040_, lean_object* v_tailPos_3041_, lean_object* v_a_3042_){
_start:
{
uint8_t v_res_3043_; lean_object* v_r_3044_; 
v_res_3043_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic(v_hoverPos_3039_, v_pos_3040_, v_tailPos_3041_, v_a_3042_);
lean_dec_ref(v_a_3042_);
lean_dec(v_tailPos_3041_);
lean_dec(v_pos_3040_);
lean_dec(v_hoverPos_3039_);
v_r_3044_ = lean_box(v_res_3043_);
return v_r_3044_;
}
}
uint8_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock(lean_object* v_stx_3046_){
_start:
{
lean_object* v___x_3047_; uint8_t v___x_3048_; 
v___x_3047_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock___closed__0));
lean_inc(v_stx_3046_);
v___x_3048_ = l_Lean_Syntax_isToken(v___x_3047_, v_stx_3046_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; lean_object* v___x_3050_; uint8_t v___x_3051_; 
v___x_3049_ = l_Lean_Syntax_getNumArgs(v_stx_3046_);
v___x_3050_ = lean_unsigned_to_nat(2u);
v___x_3051_ = lean_nat_dec_eq(v___x_3049_, v___x_3050_);
lean_dec(v___x_3049_);
if (v___x_3051_ == 0)
{
lean_dec(v_stx_3046_);
return v___x_3051_;
}
else
{
lean_object* v___x_3052_; lean_object* v___x_3053_; uint8_t v___x_3054_; 
v___x_3052_ = lean_unsigned_to_nat(0u);
v___x_3053_ = l_Lean_Syntax_getArg(v_stx_3046_, v___x_3052_);
lean_dec(v_stx_3046_);
v___x_3054_ = l_Lean_Syntax_isToken(v___x_3047_, v___x_3053_);
return v___x_3054_;
}
}
else
{
lean_dec(v_stx_3046_);
return v___x_3048_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_3046_ = stack[0].m_obj;
uint8_t v_res_3055_;
v_res_3055_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock(v_stx_3046_);
stack->m_num = v_res_3055_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock___boxed(lean_object* v_stx_3056_){
_start:
{
uint8_t v_res_3057_; lean_object* v_r_3058_; 
v_res_3057_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock(v_stx_3056_);
v_r_3058_ = lean_box(v_res_3057_);
return v_r_3058_;
}
}
uint8_t l_instBEqOption_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(lean_object* v_x_3059_, lean_object* v_x_3060_){
_start:
{
if (lean_obj_tag(v_x_3059_) == 0)
{
if (lean_obj_tag(v_x_3060_) == 0)
{
uint8_t v___x_3061_; 
v___x_3061_ = 1;
return v___x_3061_;
}
else
{
uint8_t v___x_3062_; 
v___x_3062_ = 0;
return v___x_3062_;
}
}
else
{
if (lean_obj_tag(v_x_3060_) == 0)
{
uint8_t v___x_3063_; 
v___x_3063_ = 0;
return v___x_3063_;
}
else
{
lean_object* v_val_3064_; lean_object* v_val_3065_; uint8_t v___x_3066_; 
v_val_3064_ = lean_ctor_get(v_x_3059_, 0);
v_val_3065_ = lean_ctor_get(v_x_3060_, 0);
v___x_3066_ = lean_nat_dec_eq(v_val_3064_, v_val_3065_);
return v___x_3066_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3059_ = stack[0].m_obj;
lean_object* v_x_3060_ = stack[1].m_obj;
uint8_t v_res_3067_;
v_res_3067_ = l_instBEqOption_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(v_x_3059_, v_x_3060_);
stack->m_num = v_res_3067_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4___boxed(lean_object* v_x_3068_, lean_object* v_x_3069_){
_start:
{
uint8_t v_res_3070_; lean_object* v_r_3071_; 
v_res_3070_ = l_instBEqOption_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(v_x_3068_, v_x_3069_);
lean_dec(v_x_3069_);
lean_dec(v_x_3068_);
v_r_3071_ = lean_box(v_res_3070_);
return v_r_3071_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(lean_object* v_hoverCol_3072_, lean_object* v_col_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_){
_start:
{
if (lean_obj_tag(v_a_3074_) == 0)
{
lean_object* v___x_3076_; 
v___x_3076_ = l_List_reverse___redArg(v_a_3075_);
return v___x_3076_;
}
else
{
lean_object* v_head_3077_; lean_object* v_tail_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3102_; 
v_head_3077_ = lean_ctor_get(v_a_3074_, 0);
v_tail_3078_ = lean_ctor_get(v_a_3074_, 1);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_a_3074_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3080_ = v_a_3074_;
v_isShared_3081_ = v_isSharedCheck_3102_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_tail_3078_);
lean_inc(v_head_3077_);
lean_dec(v_a_3074_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3102_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___y_3083_; uint8_t v_hangingBy_3088_; 
v_hangingBy_3088_ = lean_ctor_get_uint8(v_head_3077_, sizeof(void*)*3 + 2);
if (v_hangingBy_3088_ == 0)
{
v___y_3083_ = v_head_3077_;
goto v___jp_3082_;
}
else
{
lean_object* v_ctxInfo_3089_; lean_object* v_tacticInfo_3090_; uint8_t v_useAfter_3091_; lean_object* v_priority_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3101_; 
v_ctxInfo_3089_ = lean_ctor_get(v_head_3077_, 0);
v_tacticInfo_3090_ = lean_ctor_get(v_head_3077_, 1);
v_useAfter_3091_ = lean_ctor_get_uint8(v_head_3077_, sizeof(void*)*3);
v_priority_3092_ = lean_ctor_get(v_head_3077_, 2);
v_isSharedCheck_3101_ = !lean_is_exclusive(v_head_3077_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3094_ = v_head_3077_;
v_isShared_3095_ = v_isSharedCheck_3101_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_priority_3092_);
lean_inc(v_tacticInfo_3090_);
lean_inc(v_ctxInfo_3089_);
lean_dec(v_head_3077_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3101_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
uint8_t v___x_3096_; uint8_t v___x_3097_; lean_object* v___x_3099_; 
v___x_3096_ = lean_nat_dec_le(v_hoverCol_3072_, v_col_3073_);
v___x_3097_ = 0;
if (v_isShared_3095_ == 0)
{
v___x_3099_ = v___x_3094_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_ctxInfo_3089_);
lean_ctor_set(v_reuseFailAlloc_3100_, 1, v_tacticInfo_3090_);
lean_ctor_set(v_reuseFailAlloc_3100_, 2, v_priority_3092_);
lean_ctor_set_uint8(v_reuseFailAlloc_3100_, sizeof(void*)*3, v_useAfter_3091_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
lean_ctor_set_uint8(v___x_3099_, sizeof(void*)*3 + 1, v___x_3096_);
lean_ctor_set_uint8(v___x_3099_, sizeof(void*)*3 + 2, v___x_3097_);
v___y_3083_ = v___x_3099_;
goto v___jp_3082_;
}
}
}
v___jp_3082_:
{
lean_object* v___x_3085_; 
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 1, v_a_3075_);
lean_ctor_set(v___x_3080_, 0, v___y_3083_);
v___x_3085_ = v___x_3080_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v___y_3083_);
lean_ctor_set(v_reuseFailAlloc_3087_, 1, v_a_3075_);
v___x_3085_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
v_a_3074_ = v_tail_3078_;
v_a_3075_ = v___x_3085_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0___boxed(lean_object* v_hoverCol_3103_, lean_object* v_col_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(v_hoverCol_3103_, v_col_3104_, v_a_3105_, v_a_3106_);
lean_dec(v_col_3104_);
lean_dec(v_hoverCol_3103_);
return v_res_3107_;
}
}
uint8_t l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(lean_object* v_x_3108_){
_start:
{
if (lean_obj_tag(v_x_3108_) == 0)
{
uint8_t v___x_3109_; 
v___x_3109_ = 1;
return v___x_3109_;
}
else
{
lean_object* v_head_3110_; uint8_t v_indented_3111_; 
v_head_3110_ = lean_ctor_get(v_x_3108_, 0);
v_indented_3111_ = lean_ctor_get_uint8(v_head_3110_, sizeof(void*)*3 + 1);
if (v_indented_3111_ == 0)
{
return v_indented_3111_;
}
else
{
lean_object* v_tail_3112_; 
v_tail_3112_ = lean_ctor_get(v_x_3108_, 1);
v_x_3108_ = v_tail_3112_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3108_ = stack[0].m_obj;
uint8_t v_res_3114_;
v_res_3114_ = l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(v_x_3108_);
stack->m_num = v_res_3114_;
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1___boxed(lean_object* v_x_3115_){
_start:
{
uint8_t v_res_3116_; lean_object* v_r_3117_; 
v_res_3116_ = l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(v_x_3115_);
lean_dec(v_x_3115_);
v_r_3117_ = lean_box(v_res_3116_);
return v_r_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0(lean_object* v_text_3118_, lean_object* v_column_3119_, lean_object* v_hoverPos_3120_, lean_object* v_ctx_3121_, lean_object* v_i_3122_, lean_object* v_cs_3123_, lean_object* v_gs_3124_){
_start:
{
if (lean_obj_tag(v_i_3122_) == 0)
{
lean_object* v_i_3125_; lean_object* v___x_3126_; 
v_i_3125_ = lean_ctor_get(v_i_3122_, 0);
v___x_3126_ = l_Lean_Elab_Info_pos_x3f(v_i_3122_);
if (lean_obj_tag(v___x_3126_) == 1)
{
lean_object* v_val_3127_; lean_object* v___x_3128_; 
v_val_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_val_3127_);
lean_dec_ref_known(v___x_3126_, 1);
v___x_3128_ = l_Lean_Elab_Info_tailPos_x3f(v_i_3122_);
if (lean_obj_tag(v___x_3128_) == 1)
{
lean_object* v_val_3129_; lean_object* v___x_3130_; lean_object* v_column_3131_; lean_object* v_source_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3182_; 
v_val_3129_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_val_3129_);
lean_dec_ref_known(v___x_3128_, 1);
lean_inc_ref(v_text_3118_);
v___x_3130_ = l_Lean_FileMap_toPosition(v_text_3118_, v_val_3127_);
v_column_3131_ = lean_ctor_get(v___x_3130_, 1);
lean_inc(v_column_3131_);
lean_dec_ref(v___x_3130_);
v_source_3132_ = lean_ctor_get(v_text_3118_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v_text_3118_);
if (v_isSharedCheck_3182_ == 0)
{
lean_object* v_unused_3183_; 
v_unused_3183_ = lean_ctor_get(v_text_3118_, 1);
lean_dec(v_unused_3183_);
v___x_3134_ = v_text_3118_;
v_isShared_3135_ = v_isSharedCheck_3182_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_source_3132_);
lean_dec(v_text_3118_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3182_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3136_; uint8_t v___y_3138_; uint8_t v___y_3139_; uint8_t v___y_3140_; lean_object* v___y_3141_; lean_object* v_gs_3146_; lean_object* v___x_3147_; lean_object* v_trailSize_3148_; lean_object* v___x_3149_; uint8_t v___y_3151_; uint8_t v___y_3158_; uint8_t v___y_3165_; uint8_t v___y_3167_; uint8_t v___y_3172_; uint8_t v___x_3173_; 
v___x_3136_ = lean_box(0);
v_gs_3146_ = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__0(v_column_3119_, v_column_3131_, v_gs_3124_, v___x_3136_);
v___x_3147_ = l_Lean_Elab_Info_stx(v_i_3122_);
v_trailSize_3148_ = l_Lean_Syntax_getTrailingSize(v___x_3147_);
v___x_3149_ = lean_nat_add(v_val_3129_, v_trailSize_3148_);
v___x_3173_ = lean_nat_dec_le(v_val_3127_, v_hoverPos_3120_);
if (v___x_3173_ == 0)
{
lean_dec(v_trailSize_3148_);
lean_dec_ref(v_source_3132_);
v___y_3172_ = v___x_3173_;
goto v___jp_3171_;
}
else
{
lean_object* v___x_3174_; uint8_t v_atEOF_3175_; lean_object* v___y_3177_; lean_object* v___x_3180_; uint8_t v___x_3181_; 
v___x_3174_ = lean_string_utf8_byte_size(v_source_3132_);
lean_dec_ref(v_source_3132_);
v_atEOF_3175_ = lean_nat_dec_eq(v___x_3149_, v___x_3174_);
v___x_3180_ = lean_unsigned_to_nat(1u);
v___x_3181_ = lean_nat_dec_le(v___x_3180_, v_trailSize_3148_);
if (v___x_3181_ == 0)
{
lean_dec(v_trailSize_3148_);
v___y_3177_ = v___x_3180_;
goto v___jp_3176_;
}
else
{
v___y_3177_ = v_trailSize_3148_;
goto v___jp_3176_;
}
v___jp_3176_:
{
lean_object* v___x_3178_; uint8_t v___x_3179_; 
v___x_3178_ = lean_nat_add(v_val_3129_, v___y_3177_);
lean_dec(v___y_3177_);
v___x_3179_ = lean_nat_dec_lt(v_hoverPos_3120_, v___x_3178_);
lean_dec(v___x_3178_);
if (v___x_3179_ == 0)
{
v___y_3172_ = v_atEOF_3175_;
goto v___jp_3171_;
}
else
{
v___y_3167_ = v___x_3179_;
goto v___jp_3166_;
}
}
}
v___jp_3137_:
{
lean_object* v___x_3142_; lean_object* v___x_3144_; 
lean_inc_ref(v_i_3125_);
v___x_3142_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3142_, 0, v_ctx_3121_);
lean_ctor_set(v___x_3142_, 1, v_i_3125_);
lean_ctor_set(v___x_3142_, 2, v___y_3141_);
lean_ctor_set_uint8(v___x_3142_, sizeof(void*)*3, v___y_3140_);
lean_ctor_set_uint8(v___x_3142_, sizeof(void*)*3 + 1, v___y_3138_);
lean_ctor_set_uint8(v___x_3142_, sizeof(void*)*3 + 2, v___y_3139_);
if (v_isShared_3135_ == 0)
{
lean_ctor_set_tag(v___x_3134_, 1);
lean_ctor_set(v___x_3134_, 1, v___x_3136_);
lean_ctor_set(v___x_3134_, 0, v___x_3142_);
v___x_3144_ = v___x_3134_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3142_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v___x_3136_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
v___jp_3150_:
{
uint8_t v___x_3152_; uint8_t v___x_3153_; uint8_t v___x_3154_; 
v___x_3152_ = lean_nat_dec_lt(v_column_3119_, v_column_3131_);
lean_dec(v_column_3131_);
v___x_3153_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_isByBlock(v___x_3147_);
v___x_3154_ = lean_nat_dec_eq(v_hoverPos_3120_, v___x_3149_);
lean_dec(v___x_3149_);
if (v___x_3154_ == 0)
{
lean_object* v___x_3155_; 
v___x_3155_ = lean_unsigned_to_nat(1u);
v___y_3138_ = v___x_3152_;
v___y_3139_ = v___x_3153_;
v___y_3140_ = v___y_3151_;
v___y_3141_ = v___x_3155_;
goto v___jp_3137_;
}
else
{
lean_object* v___x_3156_; 
v___x_3156_ = lean_unsigned_to_nat(0u);
v___y_3138_ = v___x_3152_;
v___y_3139_ = v___x_3153_;
v___y_3140_ = v___y_3151_;
v___y_3141_ = v___x_3156_;
goto v___jp_3137_;
}
}
v___jp_3157_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; uint8_t v___x_3161_; 
v___x_3159_ = lean_unsigned_to_nat(1u);
v___x_3160_ = lean_nat_add(v_val_3127_, v___x_3159_);
v___x_3161_ = lean_nat_dec_le(v___x_3160_, v_hoverPos_3120_);
lean_dec(v___x_3160_);
if (v___x_3161_ == 0)
{
lean_dec(v_val_3129_);
lean_dec(v_val_3127_);
v___y_3151_ = v___x_3161_;
goto v___jp_3150_;
}
else
{
uint8_t v___x_3162_; 
v___x_3162_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_goalsAt_x3f_hasNestedTactic_spec__0(v_hoverPos_3120_, v_val_3127_, v_val_3129_, v_cs_3123_);
lean_dec(v_val_3129_);
lean_dec(v_val_3127_);
if (v___x_3162_ == 0)
{
v___y_3151_ = v___y_3158_;
goto v___jp_3150_;
}
else
{
uint8_t v___x_3163_; 
v___x_3163_ = 0;
v___y_3151_ = v___x_3163_;
goto v___jp_3150_;
}
}
}
v___jp_3164_:
{
if (v___y_3165_ == 0)
{
lean_dec(v___x_3149_);
lean_dec(v___x_3147_);
lean_del_object(v___x_3134_);
lean_dec(v_column_3131_);
lean_dec(v_val_3129_);
lean_dec(v_val_3127_);
lean_dec_ref(v_ctx_3121_);
return v_gs_3146_;
}
else
{
lean_dec(v_gs_3146_);
v___y_3158_ = v___y_3165_;
goto v___jp_3157_;
}
}
v___jp_3166_:
{
uint8_t v___x_3168_; 
v___x_3168_ = l_List_isEmpty___redArg(v_gs_3146_);
if (v___x_3168_ == 0)
{
uint8_t v___x_3169_; 
v___x_3169_ = lean_nat_dec_le(v_val_3129_, v_hoverPos_3120_);
if (v___x_3169_ == 0)
{
v___y_3165_ = v___x_3169_;
goto v___jp_3164_;
}
else
{
uint8_t v___x_3170_; 
v___x_3170_ = l_List_all___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__1(v_gs_3146_);
v___y_3165_ = v___x_3170_;
goto v___jp_3164_;
}
}
else
{
lean_dec(v_gs_3146_);
v___y_3158_ = v___y_3167_;
goto v___jp_3157_;
}
}
v___jp_3171_:
{
if (v___y_3172_ == 0)
{
lean_dec(v___x_3149_);
lean_dec(v___x_3147_);
lean_del_object(v___x_3134_);
lean_dec(v_column_3131_);
lean_dec(v_val_3129_);
lean_dec(v_val_3127_);
lean_dec_ref(v_ctx_3121_);
return v_gs_3146_;
}
else
{
v___y_3167_ = v___y_3172_;
goto v___jp_3166_;
}
}
}
}
else
{
lean_dec(v___x_3128_);
lean_dec(v_val_3127_);
lean_dec_ref(v_ctx_3121_);
lean_dec_ref(v_text_3118_);
return v_gs_3124_;
}
}
else
{
lean_dec(v___x_3126_);
lean_dec_ref(v_ctx_3121_);
lean_dec_ref(v_text_3118_);
return v_gs_3124_;
}
}
else
{
lean_dec_ref(v_ctx_3121_);
lean_dec_ref(v_text_3118_);
return v_gs_3124_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0___boxed(lean_object* v_text_3184_, lean_object* v_column_3185_, lean_object* v_hoverPos_3186_, lean_object* v_ctx_3187_, lean_object* v_i_3188_, lean_object* v_cs_3189_, lean_object* v_gs_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0(v_text_3184_, v_column_3185_, v_hoverPos_3186_, v_ctx_3187_, v_i_3188_, v_cs_3189_, v_gs_3190_);
lean_dec_ref(v_cs_3189_);
lean_dec_ref(v_i_3188_);
lean_dec(v_hoverPos_3186_);
lean_dec(v_column_3185_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3_spec__3(lean_object* v_x_3192_, lean_object* v_x_3193_){
_start:
{
if (lean_obj_tag(v_x_3193_) == 0)
{
lean_inc(v_x_3192_);
return v_x_3192_;
}
else
{
lean_object* v_head_3194_; lean_object* v_tail_3195_; uint8_t v___x_3196_; 
v_head_3194_ = lean_ctor_get(v_x_3193_, 0);
v_tail_3195_ = lean_ctor_get(v_x_3193_, 1);
v___x_3196_ = lean_nat_dec_le(v_x_3192_, v_head_3194_);
if (v___x_3196_ == 0)
{
v_x_3193_ = v_tail_3195_;
goto _start;
}
else
{
v_x_3192_ = v_head_3194_;
v_x_3193_ = v_tail_3195_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3_spec__3___boxed(lean_object* v_x_3199_, lean_object* v_x_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3_spec__3(v_x_3199_, v_x_3200_);
lean_dec(v_x_3200_);
lean_dec(v_x_3199_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(lean_object* v_x_3202_){
_start:
{
if (lean_obj_tag(v_x_3202_) == 0)
{
lean_object* v___x_3203_; 
v___x_3203_ = lean_box(0);
return v___x_3203_;
}
else
{
lean_object* v_head_3204_; lean_object* v_tail_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v_head_3204_ = lean_ctor_get(v_x_3202_, 0);
v_tail_3205_ = lean_ctor_get(v_x_3202_, 1);
v___x_3206_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3_spec__3(v_head_3204_, v_tail_3205_);
v___x_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3206_);
return v___x_3207_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3___boxed(lean_object* v_x_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(v_x_3208_);
lean_dec(v_x_3208_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2(lean_object* v_a_3210_, lean_object* v_a_3211_){
_start:
{
if (lean_obj_tag(v_a_3210_) == 0)
{
lean_object* v___x_3212_; 
v___x_3212_ = l_List_reverse___redArg(v_a_3211_);
return v___x_3212_;
}
else
{
lean_object* v_head_3213_; lean_object* v_tail_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3223_; 
v_head_3213_ = lean_ctor_get(v_a_3210_, 0);
v_tail_3214_ = lean_ctor_get(v_a_3210_, 1);
v_isSharedCheck_3223_ = !lean_is_exclusive(v_a_3210_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3216_ = v_a_3210_;
v_isShared_3217_ = v_isSharedCheck_3223_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_tail_3214_);
lean_inc(v_head_3213_);
lean_dec(v_a_3210_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3223_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v_priority_3218_; lean_object* v___x_3220_; 
v_priority_3218_ = lean_ctor_get(v_head_3213_, 2);
lean_inc(v_priority_3218_);
lean_dec(v_head_3213_);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 1, v_a_3211_);
lean_ctor_set(v___x_3216_, 0, v_priority_3218_);
v___x_3220_ = v___x_3216_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_priority_3218_);
lean_ctor_set(v_reuseFailAlloc_3222_, 1, v_a_3211_);
v___x_3220_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
v_a_3210_ = v_tail_3214_;
v_a_3211_ = v___x_3220_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__5(lean_object* v_maxPrio_x3f_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_){
_start:
{
if (lean_obj_tag(v_a_3225_) == 0)
{
lean_object* v___x_3227_; 
v___x_3227_ = l_List_reverse___redArg(v_a_3226_);
return v___x_3227_;
}
else
{
lean_object* v_head_3228_; lean_object* v_tail_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3241_; 
v_head_3228_ = lean_ctor_get(v_a_3225_, 0);
v_tail_3229_ = lean_ctor_get(v_a_3225_, 1);
v_isSharedCheck_3241_ = !lean_is_exclusive(v_a_3225_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3231_ = v_a_3225_;
v_isShared_3232_ = v_isSharedCheck_3241_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_tail_3229_);
lean_inc(v_head_3228_);
lean_dec(v_a_3225_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3241_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v_priority_3233_; lean_object* v___x_3234_; uint8_t v___x_3235_; 
v_priority_3233_ = lean_ctor_get(v_head_3228_, 2);
lean_inc(v_priority_3233_);
v___x_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3234_, 0, v_priority_3233_);
v___x_3235_ = l_instBEqOption_beq___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__4(v___x_3234_, v_maxPrio_x3f_3224_);
lean_dec_ref_known(v___x_3234_, 1);
if (v___x_3235_ == 0)
{
lean_del_object(v___x_3231_);
lean_dec(v_head_3228_);
v_a_3225_ = v_tail_3229_;
goto _start;
}
else
{
lean_object* v___x_3238_; 
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 1, v_a_3226_);
v___x_3238_ = v___x_3231_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_head_3228_);
lean_ctor_set(v_reuseFailAlloc_3240_, 1, v_a_3226_);
v___x_3238_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
v_a_3225_ = v_tail_3229_;
v_a_3226_ = v___x_3238_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__5___boxed(lean_object* v_maxPrio_x3f_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__5(v_maxPrio_x3f_3242_, v_a_3243_, v_a_3244_);
lean_dec(v_maxPrio_x3f_3242_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f(lean_object* v_text_3246_, lean_object* v_t_3247_, lean_object* v_hoverPos_3248_){
_start:
{
lean_object* v___x_3249_; lean_object* v_column_3250_; lean_object* v___f_3251_; lean_object* v_gs_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v_maxPrio_x3f_3255_; lean_object* v___x_3256_; 
lean_inc_ref(v_text_3246_);
v___x_3249_ = l_Lean_FileMap_toPosition(v_text_3246_, v_hoverPos_3248_);
v_column_3250_ = lean_ctor_get(v___x_3249_, 1);
lean_inc(v_column_3250_);
lean_dec_ref(v___x_3249_);
v___f_3251_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_goalsAt_x3f___lam__0___boxed), 7, 3);
lean_closure_set(v___f_3251_, 0, v_text_3246_);
lean_closure_set(v___f_3251_, 1, v_column_3250_);
lean_closure_set(v___f_3251_, 2, v_hoverPos_3248_);
v_gs_3252_ = l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg(v___f_3251_, v_t_3247_);
v___x_3253_ = lean_box(0);
lean_inc(v_gs_3252_);
v___x_3254_ = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__2(v_gs_3252_, v___x_3253_);
v_maxPrio_x3f_3255_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__3(v___x_3254_);
lean_dec(v___x_3254_);
v___x_3256_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_goalsAt_x3f_spec__5(v_maxPrio_x3f_3255_, v_gs_3252_, v___x_3253_);
lean_dec(v_maxPrio_x3f_3255_);
return v___x_3256_;
}
}
lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(lean_object* v___x_3257_, uint8_t v___y_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_){
_start:
{
if (lean_obj_tag(v_a_3259_) == 0)
{
lean_object* v___x_3261_; 
v___x_3261_ = l_List_reverse___redArg(v_a_3260_);
return v___x_3261_;
}
else
{
lean_object* v_head_3262_; lean_object* v_snd_3263_; lean_object* v_tail_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3279_; 
v_head_3262_ = lean_ctor_get(v_a_3259_, 0);
lean_inc(v_head_3262_);
v_snd_3263_ = lean_ctor_get(v_head_3262_, 1);
v_tail_3264_ = lean_ctor_get(v_a_3259_, 1);
v_isSharedCheck_3279_ = !lean_is_exclusive(v_a_3259_);
if (v_isSharedCheck_3279_ == 0)
{
lean_object* v_unused_3280_; 
v_unused_3280_ = lean_ctor_get(v_a_3259_, 0);
lean_dec(v_unused_3280_);
v___x_3266_ = v_a_3259_;
v_isShared_3267_ = v_isSharedCheck_3279_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_tail_3264_);
lean_dec(v_a_3259_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3279_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v_info_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; uint8_t v___x_3272_; 
v_info_3268_ = lean_ctor_get(v_snd_3263_, 1);
v___x_3269_ = l_Lean_Elab_Info_stx(v_info_3268_);
v___x_3270_ = lean_unsigned_to_nat(0u);
v___x_3271_ = l_Lean_Syntax_getArg(v___x_3257_, v___x_3270_);
v___x_3272_ = l_Lean_Syntax_structEq(v___x_3269_, v___x_3271_);
lean_dec(v___x_3271_);
lean_dec(v___x_3269_);
if (v___x_3272_ == 0)
{
if (v___y_3258_ == 0)
{
lean_del_object(v___x_3266_);
lean_dec(v_head_3262_);
v_a_3259_ = v_tail_3264_;
goto _start;
}
else
{
lean_object* v___x_3275_; 
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 1, v_a_3260_);
v___x_3275_ = v___x_3266_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_head_3262_);
lean_ctor_set(v_reuseFailAlloc_3277_, 1, v_a_3260_);
v___x_3275_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
v_a_3259_ = v_tail_3264_;
v_a_3260_ = v___x_3275_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_3266_);
lean_dec(v_head_3262_);
v_a_3259_ = v_tail_3264_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3257_ = stack[0].m_obj;
uint8_t v___y_3258_ = stack[1].m_num;
lean_object* v_a_3259_ = stack[2].m_obj;
lean_object* v_a_3260_ = stack[3].m_obj;
lean_object* v_res_3281_;
v_res_3281_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(v___x_3257_, v___y_3258_, v_a_3259_, v_a_3260_);
stack->m_obj
 = v_res_3281_;
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0___boxed(lean_object* v___x_3282_, lean_object* v___y_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_){
_start:
{
uint8_t v___y_1198__boxed_3286_; lean_object* v_res_3287_; 
v___y_1198__boxed_3286_ = lean_unbox(v___y_3283_);
v_res_3287_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(v___x_3282_, v___y_1198__boxed_3286_, v_a_3284_, v_a_3285_);
lean_dec(v___x_3282_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0(lean_object* v_ctx_3294_, lean_object* v_info_3295_, lean_object* v_children_3296_, lean_object* v_results_3297_){
_start:
{
lean_object* v___x_3298_; uint8_t v___y_3300_; lean_object* v___x_3303_; uint8_t v___x_3304_; 
v___x_3298_ = l_Lean_Elab_Info_stx(v_info_3295_);
v___x_3303_ = ((lean_object*)(l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___closed__1));
lean_inc(v___x_3298_);
v___x_3304_ = l_Lean_Syntax_isOfKind(v___x_3298_, v___x_3303_);
if (v___x_3304_ == 0)
{
v___y_3300_ = v___x_3304_;
goto v___jp_3299_;
}
else
{
lean_object* v___x_3305_; lean_object* v___x_3306_; uint8_t v___x_3307_; 
v___x_3305_ = lean_unsigned_to_nat(0u);
v___x_3306_ = l_Lean_Syntax_getArg(v___x_3298_, v___x_3305_);
v___x_3307_ = l_Lean_Syntax_isIdent(v___x_3306_);
lean_dec(v___x_3306_);
v___y_3300_ = v___x_3307_;
goto v___jp_3299_;
}
v___jp_3299_:
{
if (v___y_3300_ == 0)
{
lean_dec(v___x_3298_);
return v_results_3297_;
}
else
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = lean_box(0);
v___x_3302_ = l_List_filterTR_loop___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__0(v___x_3298_, v___y_3300_, v_results_3297_, v___x_3301_);
lean_dec(v___x_3298_);
return v___x_3302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0___boxed(lean_object* v_ctx_3308_, lean_object* v_info_3309_, lean_object* v_children_3310_, lean_object* v_results_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_Lean_Elab_InfoTree_termGoalAt_x3f___lam__0(v_ctx_3308_, v_info_3309_, v_children_3310_, v_results_3311_);
lean_dec_ref(v_children_3310_);
lean_dec_ref(v_info_3309_);
lean_dec_ref(v_ctx_3308_);
return v_res_3312_;
}
}
uint8_t l_instBEqOption_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(lean_object* v_x_3313_, lean_object* v_x_3314_){
_start:
{
if (lean_obj_tag(v_x_3313_) == 0)
{
if (lean_obj_tag(v_x_3314_) == 0)
{
uint8_t v___x_3315_; 
v___x_3315_ = 1;
return v___x_3315_;
}
else
{
uint8_t v___x_3316_; 
v___x_3316_ = 0;
return v___x_3316_;
}
}
else
{
if (lean_obj_tag(v_x_3314_) == 0)
{
uint8_t v___x_3317_; 
v___x_3317_ = 0;
return v___x_3317_;
}
else
{
lean_object* v_val_3318_; lean_object* v_val_3319_; uint8_t v___x_3320_; 
v_val_3318_ = lean_ctor_get(v_x_3313_, 0);
v_val_3319_ = lean_ctor_get(v_x_3314_, 0);
v___x_3320_ = l_Lean_Elab_instBEqHoverableInfoPrio_beq(v_val_3318_, v_val_3319_);
return v___x_3320_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3313_ = stack[0].m_obj;
lean_object* v_x_3314_ = stack[1].m_obj;
uint8_t v_res_3321_;
v_res_3321_ = l_instBEqOption_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(v_x_3313_, v_x_3314_);
stack->m_num = v_res_3321_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4___boxed(lean_object* v_x_3322_, lean_object* v_x_3323_){
_start:
{
uint8_t v_res_3324_; lean_object* v_r_3325_; 
v_res_3324_ = l_instBEqOption_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(v_x_3322_, v_x_3323_);
lean_dec(v_x_3323_);
lean_dec(v_x_3322_);
v_r_3325_ = lean_box(v_res_3324_);
return v_r_3325_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5(lean_object* v_maxPrio_x3f_3326_, lean_object* v_x_3327_){
_start:
{
if (lean_obj_tag(v_x_3327_) == 0)
{
lean_object* v___x_3328_; 
v___x_3328_ = lean_box(0);
return v___x_3328_;
}
else
{
lean_object* v_head_3329_; lean_object* v_tail_3330_; lean_object* v_fst_3331_; lean_object* v___x_3332_; uint8_t v___x_3333_; 
v_head_3329_ = lean_ctor_get(v_x_3327_, 0);
v_tail_3330_ = lean_ctor_get(v_x_3327_, 1);
v_fst_3331_ = lean_ctor_get(v_head_3329_, 0);
lean_inc(v_fst_3331_);
v___x_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3332_, 0, v_fst_3331_);
v___x_3333_ = l_instBEqOption_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__4(v___x_3332_, v_maxPrio_x3f_3326_);
lean_dec_ref_known(v___x_3332_, 1);
if (v___x_3333_ == 0)
{
v_x_3327_ = v_tail_3330_;
goto _start;
}
else
{
lean_object* v___x_3335_; 
lean_inc(v_head_3329_);
v___x_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3335_, 0, v_head_3329_);
return v___x_3335_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5___boxed(lean_object* v_maxPrio_x3f_3336_, lean_object* v_x_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5(v_maxPrio_x3f_3336_, v_x_3337_);
lean_dec(v_x_3337_);
lean_dec(v_maxPrio_x3f_3336_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(lean_object* v_x_3339_, lean_object* v_x_3340_){
_start:
{
if (lean_obj_tag(v_x_3340_) == 0)
{
lean_inc_ref(v_x_3339_);
return v_x_3339_;
}
else
{
lean_object* v_head_3341_; lean_object* v_tail_3342_; uint8_t v___x_3343_; 
v_head_3341_ = lean_ctor_get(v_x_3340_, 0);
v_tail_3342_ = lean_ctor_get(v_x_3340_, 1);
v___x_3343_ = l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(v_x_3339_, v_head_3341_);
if (v___x_3343_ == 2)
{
v_x_3340_ = v_tail_3342_;
goto _start;
}
else
{
v_x_3339_ = v_head_3341_;
v_x_3340_ = v_tail_3342_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4___boxed(lean_object* v_x_3346_, lean_object* v_x_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(v_x_3346_, v_x_3347_);
lean_dec(v_x_3347_);
lean_dec_ref(v_x_3346_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(lean_object* v_x_3349_){
_start:
{
if (lean_obj_tag(v_x_3349_) == 0)
{
lean_object* v___x_3350_; 
v___x_3350_ = lean_box(0);
return v___x_3350_;
}
else
{
lean_object* v_head_3351_; lean_object* v_tail_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v_head_3351_ = lean_ctor_get(v_x_3349_, 0);
v_tail_3352_ = lean_ctor_get(v_x_3349_, 1);
v___x_3353_ = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3_spec__4(v_head_3351_, v_tail_3352_);
v___x_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
return v___x_3354_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3___boxed(lean_object* v_x_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(v_x_3355_);
lean_dec(v_x_3355_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__1(lean_object* v_a_3357_, lean_object* v_a_3358_){
_start:
{
if (lean_obj_tag(v_a_3357_) == 0)
{
lean_object* v___x_3359_; 
v___x_3359_ = lean_array_to_list(v_a_3358_);
return v___x_3359_;
}
else
{
lean_object* v_head_3360_; 
v_head_3360_ = lean_ctor_get(v_a_3357_, 0);
if (lean_obj_tag(v_head_3360_) == 0)
{
lean_object* v_tail_3361_; 
v_tail_3361_ = lean_ctor_get(v_a_3357_, 1);
lean_inc(v_tail_3361_);
lean_dec_ref_known(v_a_3357_, 2);
v_a_3357_ = v_tail_3361_;
goto _start;
}
else
{
lean_object* v_val_3363_; 
v_val_3363_ = lean_ctor_get(v_head_3360_, 0);
if (lean_obj_tag(v_val_3363_) == 0)
{
lean_object* v_tail_3364_; 
v_tail_3364_ = lean_ctor_get(v_a_3357_, 1);
lean_inc(v_tail_3364_);
lean_dec_ref_known(v_a_3357_, 2);
v_a_3357_ = v_tail_3364_;
goto _start;
}
else
{
lean_object* v_tail_3366_; lean_object* v_val_3367_; lean_object* v___x_3368_; 
lean_inc_ref(v_val_3363_);
v_tail_3366_ = lean_ctor_get(v_a_3357_, 1);
lean_inc(v_tail_3366_);
lean_dec_ref_known(v_a_3357_, 2);
v_val_3367_ = lean_ctor_get(v_val_3363_, 0);
lean_inc(v_val_3367_);
lean_dec_ref_known(v_val_3363_, 1);
v___x_3368_ = lean_array_push(v_a_3358_, v_val_3367_);
v_a_3357_ = v_tail_3366_;
v_a_3358_ = v___x_3368_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__2(lean_object* v_a_3370_, lean_object* v_a_3371_){
_start:
{
if (lean_obj_tag(v_a_3370_) == 0)
{
lean_object* v___x_3372_; 
v___x_3372_ = l_List_reverse___redArg(v_a_3371_);
return v___x_3372_;
}
else
{
lean_object* v_head_3373_; lean_object* v_tail_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3383_; 
v_head_3373_ = lean_ctor_get(v_a_3370_, 0);
v_tail_3374_ = lean_ctor_get(v_a_3370_, 1);
v_isSharedCheck_3383_ = !lean_is_exclusive(v_a_3370_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3376_ = v_a_3370_;
v_isShared_3377_ = v_isSharedCheck_3383_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_tail_3374_);
lean_inc(v_head_3373_);
lean_dec(v_a_3370_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3383_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v_fst_3378_; lean_object* v___x_3380_; 
v_fst_3378_ = lean_ctor_get(v_head_3373_, 0);
lean_inc(v_fst_3378_);
lean_dec(v_head_3373_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 1, v_a_3371_);
lean_ctor_set(v___x_3376_, 0, v_fst_3378_);
v___x_3380_ = v___x_3376_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_fst_3378_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_a_3371_);
v___x_3380_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
v_a_3370_ = v_tail_3374_;
v_a_3371_ = v___x_3380_;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1(lean_object* v_filter_3384_, lean_object* v_hoverPos_3385_, uint8_t v_includeStop_3386_, lean_object* v_ctx_3387_, lean_object* v_info_3388_, lean_object* v_children_3389_, lean_object* v_results_3390_){
_start:
{
lean_object* v___y_3392_; uint8_t v___y_3393_; uint8_t v___y_3394_; uint8_t v___y_3395_; lean_object* v___y_3401_; uint8_t v___y_3402_; uint8_t v___y_3403_; uint8_t v___y_3404_; uint8_t v___y_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v_maxPrio_x3f_3411_; lean_object* v_bestResult_x3f_3412_; 
v___x_3406_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__4___closed__0));
v___x_3407_ = l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__1(v_results_3390_, v___x_3406_);
lean_inc_ref(v_children_3389_);
lean_inc_ref(v_info_3388_);
lean_inc_ref(v_ctx_3387_);
v___x_3408_ = lean_apply_4(v_filter_3384_, v_ctx_3387_, v_info_3388_, v_children_3389_, v___x_3407_);
v___x_3409_ = lean_box(0);
lean_inc(v___x_3408_);
v___x_3410_ = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__2(v___x_3408_, v___x_3409_);
v_maxPrio_x3f_3411_ = l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__3(v___x_3410_);
lean_dec(v___x_3410_);
v_bestResult_x3f_3412_ = l_List_find_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_spec__5(v_maxPrio_x3f_3411_, v___x_3408_);
lean_dec(v___x_3408_);
lean_dec(v_maxPrio_x3f_3411_);
if (lean_obj_tag(v_bestResult_x3f_3412_) == 1)
{
lean_dec_ref(v_children_3389_);
lean_dec_ref(v_info_3388_);
lean_dec_ref(v_ctx_3387_);
return v_bestResult_x3f_3412_;
}
else
{
lean_object* v___x_3413_; uint8_t v___y_3415_; uint8_t v___y_3416_; uint8_t v___y_3417_; uint8_t v___y_3431_; lean_object* v___x_3435_; uint8_t v___x_3436_; 
lean_dec(v_bestResult_x3f_3412_);
v___x_3413_ = l_Lean_Elab_Info_stx(v_info_3388_);
v___x_3435_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__1));
lean_inc(v___x_3413_);
v___x_3436_ = l_Lean_Syntax_isOfKind(v___x_3413_, v___x_3435_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; 
lean_inc_ref(v_info_3388_);
v___x_3437_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_3388_);
if (lean_obj_tag(v___x_3437_) == 0)
{
v___y_3431_ = v___x_3436_;
goto v___jp_3430_;
}
else
{
lean_object* v_val_3438_; lean_object* v_elaborator_3439_; lean_object* v___x_3440_; uint8_t v___x_3441_; 
v_val_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_val_3438_);
lean_dec_ref_known(v___x_3437_, 1);
v_elaborator_3439_ = lean_ctor_get(v_val_3438_, 0);
lean_inc(v_elaborator_3439_);
lean_dec(v_val_3438_);
v___x_3440_ = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___redArg___lam__3___closed__6));
v___x_3441_ = lean_name_eq(v_elaborator_3439_, v___x_3440_);
lean_dec(v_elaborator_3439_);
v___y_3431_ = v___x_3441_;
goto v___jp_3430_;
}
}
else
{
v___y_3431_ = v___x_3436_;
goto v___jp_3430_;
}
v___jp_3414_:
{
lean_object* v___x_3418_; 
v___x_3418_ = l_Lean_Syntax_getRange_x3f(v___x_3413_, v___y_3416_);
lean_dec(v___x_3413_);
if (lean_obj_tag(v___x_3418_) == 1)
{
lean_object* v_val_3419_; uint8_t v___x_3420_; 
v_val_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_val_3419_);
lean_dec_ref_known(v___x_3418_, 1);
v___x_3420_ = l_Lean_Syntax_Range_contains(v_val_3419_, v_hoverPos_3385_, v_includeStop_3386_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; 
lean_dec(v_val_3419_);
lean_dec_ref(v_children_3389_);
lean_dec_ref(v_info_3388_);
lean_dec_ref(v_ctx_3387_);
v___x_3421_ = lean_box(0);
return v___x_3421_;
}
else
{
if (v___y_3417_ == 0)
{
lean_object* v___x_3422_; 
lean_dec(v_val_3419_);
lean_dec_ref(v_children_3389_);
lean_dec_ref(v_info_3388_);
lean_dec_ref(v_ctx_3387_);
v___x_3422_ = lean_box(0);
return v___x_3422_;
}
else
{
lean_object* v_start_3423_; lean_object* v_stop_3424_; uint8_t v_decide_3425_; lean_object* v___x_3426_; 
v_start_3423_ = lean_ctor_get(v_val_3419_, 0);
lean_inc(v_start_3423_);
v_stop_3424_ = lean_ctor_get(v_val_3419_, 1);
lean_inc(v_stop_3424_);
lean_dec(v_val_3419_);
v_decide_3425_ = lean_nat_dec_eq(v_stop_3424_, v_hoverPos_3385_);
v___x_3426_ = lean_nat_sub(v_stop_3424_, v_start_3423_);
lean_dec(v_start_3423_);
lean_dec(v_stop_3424_);
if (lean_obj_tag(v_info_3388_) == 1)
{
lean_object* v_i_3427_; lean_object* v_expr_3428_; 
v_i_3427_ = lean_ctor_get(v_info_3388_, 0);
v_expr_3428_ = lean_ctor_get(v_i_3427_, 3);
if (lean_obj_tag(v_expr_3428_) == 1)
{
v___y_3401_ = v___x_3426_;
v___y_3402_ = v___y_3415_;
v___y_3403_ = v_decide_3425_;
v___y_3404_ = v___y_3416_;
v___y_3405_ = v___y_3416_;
goto v___jp_3400_;
}
else
{
v___y_3401_ = v___x_3426_;
v___y_3402_ = v___y_3415_;
v___y_3403_ = v_decide_3425_;
v___y_3404_ = v___y_3416_;
v___y_3405_ = v___y_3415_;
goto v___jp_3400_;
}
}
else
{
v___y_3401_ = v___x_3426_;
v___y_3402_ = v___y_3415_;
v___y_3403_ = v_decide_3425_;
v___y_3404_ = v___y_3416_;
v___y_3405_ = v___y_3415_;
goto v___jp_3400_;
}
}
}
}
else
{
lean_object* v___x_3429_; 
lean_dec(v___x_3418_);
lean_dec_ref(v_children_3389_);
lean_dec_ref(v_info_3388_);
lean_dec_ref(v_ctx_3387_);
v___x_3429_ = lean_box(0);
return v___x_3429_;
}
}
v___jp_3430_:
{
if (v___y_3431_ == 0)
{
uint8_t v___x_3432_; 
v___x_3432_ = 1;
switch(lean_obj_tag(v_info_3388_))
{
case 7:
{
v___y_3415_ = v___y_3431_;
v___y_3416_ = v___x_3432_;
v___y_3417_ = v___x_3432_;
goto v___jp_3414_;
}
case 5:
{
v___y_3415_ = v___y_3431_;
v___y_3416_ = v___x_3432_;
v___y_3417_ = v___x_3432_;
goto v___jp_3414_;
}
case 6:
{
v___y_3415_ = v___y_3431_;
v___y_3416_ = v___x_3432_;
v___y_3417_ = v___x_3432_;
goto v___jp_3414_;
}
default: 
{
lean_object* v___x_3433_; 
lean_inc_ref(v_info_3388_);
v___x_3433_ = l_Lean_Elab_Info_toElabInfo_x3f(v_info_3388_);
if (lean_obj_tag(v___x_3433_) == 0)
{
v___y_3415_ = v___y_3431_;
v___y_3416_ = v___x_3432_;
v___y_3417_ = v___y_3431_;
goto v___jp_3414_;
}
else
{
lean_dec_ref_known(v___x_3433_, 1);
v___y_3415_ = v___y_3431_;
v___y_3416_ = v___x_3432_;
v___y_3417_ = v___x_3432_;
goto v___jp_3414_;
}
}
}
}
else
{
lean_object* v___x_3434_; 
lean_dec(v___x_3413_);
lean_dec_ref(v_children_3389_);
lean_dec_ref(v_info_3388_);
lean_dec_ref(v_ctx_3387_);
v___x_3434_ = lean_box(0);
return v___x_3434_;
}
}
}
v___jp_3391_:
{
lean_object* v_priority_3396_; lean_object* v_result_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v_priority_3396_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_priority_3396_, 0, v___y_3392_);
lean_ctor_set_uint8(v_priority_3396_, sizeof(void*)*1, v___y_3393_);
lean_ctor_set_uint8(v_priority_3396_, sizeof(void*)*1 + 1, v___y_3394_);
lean_ctor_set_uint8(v_priority_3396_, sizeof(void*)*1 + 2, v___y_3395_);
v_result_3397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_result_3397_, 0, v_ctx_3387_);
lean_ctor_set(v_result_3397_, 1, v_info_3388_);
lean_ctor_set(v_result_3397_, 2, v_children_3389_);
v___x_3398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3398_, 0, v_priority_3396_);
lean_ctor_set(v___x_3398_, 1, v_result_3397_);
v___x_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
return v___x_3399_;
}
v___jp_3400_:
{
if (lean_obj_tag(v_info_3388_) == 2)
{
v___y_3392_ = v___y_3401_;
v___y_3393_ = v___y_3403_;
v___y_3394_ = v___y_3405_;
v___y_3395_ = v___y_3404_;
goto v___jp_3391_;
}
else
{
v___y_3392_ = v___y_3401_;
v___y_3393_ = v___y_3403_;
v___y_3394_ = v___y_3405_;
v___y_3395_ = v___y_3402_;
goto v___jp_3391_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_filter_3384_ = stack[0].m_obj;
lean_object* v_hoverPos_3385_ = stack[1].m_obj;
uint8_t v_includeStop_3386_ = stack[2].m_num;
lean_object* v_ctx_3387_ = stack[3].m_obj;
lean_object* v_info_3388_ = stack[4].m_obj;
lean_object* v_children_3389_ = stack[5].m_obj;
lean_object* v_results_3390_ = stack[6].m_obj;
lean_object* v_res_3442_;
v_res_3442_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1(v_filter_3384_, v_hoverPos_3385_, v_includeStop_3386_, v_ctx_3387_, v_info_3388_, v_children_3389_, v_results_3390_);
stack->m_obj
 = v_res_3442_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1___boxed(lean_object* v_filter_3443_, lean_object* v_hoverPos_3444_, lean_object* v_includeStop_3445_, lean_object* v_ctx_3446_, lean_object* v_info_3447_, lean_object* v_children_3448_, lean_object* v_results_3449_){
_start:
{
uint8_t v_includeStop_boxed_3450_; lean_object* v_res_3451_; 
v_includeStop_boxed_3450_ = lean_unbox(v_includeStop_3445_);
v_res_3451_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1(v_filter_3443_, v_hoverPos_3444_, v_includeStop_boxed_3450_, v_ctx_3446_, v_info_3447_, v_children_3448_, v_results_3449_);
lean_dec(v_hoverPos_3444_);
return v_res_3451_;
}
}
lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(lean_object* v_t_3452_, lean_object* v_hoverPos_3453_, uint8_t v_includeStop_3454_, lean_object* v_filter_3455_){
_start:
{
lean_object* v___f_3456_; lean_object* v___x_3457_; lean_object* v_postNode_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___f_3456_ = ((lean_object*)(l_Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0___redArg___closed__0));
v___x_3457_ = lean_box(v_includeStop_3454_);
v_postNode_3458_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___lam__1___boxed), 7, 3);
lean_closure_set(v_postNode_3458_, 0, v_filter_3455_);
lean_closure_set(v_postNode_3458_, 1, v_hoverPos_3453_);
lean_closure_set(v_postNode_3458_, 2, v___x_3457_);
v___x_3459_ = lean_box(0);
v___x_3460_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_collectNodesBottomUpM___at___00Lean_Elab_InfoTree_collectNodesBottomUp_spec__0_spec__2___redArg(v___f_3456_, v_postNode_3458_, v___x_3459_, v_t_3452_);
if (lean_obj_tag(v___x_3460_) == 0)
{
return v___x_3459_;
}
else
{
lean_object* v_val_3461_; 
v_val_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_val_3461_);
lean_dec_ref_known(v___x_3460_, 1);
if (lean_obj_tag(v_val_3461_) == 0)
{
return v___x_3459_;
}
else
{
lean_object* v_val_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3474_; 
v_val_3462_ = lean_ctor_get(v_val_3461_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v_val_3461_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3464_ = v_val_3461_;
v_isShared_3465_ = v_isSharedCheck_3474_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_val_3462_);
lean_dec(v_val_3461_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3474_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v_snd_3466_; lean_object* v_info_3467_; lean_object* v___x_3469_; 
v_snd_3466_ = lean_ctor_get(v_val_3462_, 1);
lean_inc(v_snd_3466_);
lean_dec(v_val_3462_);
v_info_3467_ = lean_ctor_get(v_snd_3466_, 1);
lean_inc_ref(v_info_3467_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 0, v_snd_3466_);
v___x_3469_ = v___x_3464_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_snd_3466_);
v___x_3469_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
if (lean_obj_tag(v_info_3467_) == 1)
{
lean_object* v_i_3470_; lean_object* v_expr_3471_; uint8_t v___x_3472_; 
v_i_3470_ = lean_ctor_get(v_info_3467_, 0);
lean_inc_ref(v_i_3470_);
lean_dec_ref_known(v_info_3467_, 1);
v_expr_3471_ = lean_ctor_get(v_i_3470_, 3);
lean_inc_ref(v_expr_3471_);
lean_dec_ref(v_i_3470_);
v___x_3472_ = l_Lean_Expr_isSyntheticSorry(v_expr_3471_);
lean_dec_ref(v_expr_3471_);
if (v___x_3472_ == 0)
{
return v___x_3469_;
}
else
{
lean_dec_ref(v___x_3469_);
return v___x_3459_;
}
}
else
{
lean_dec_ref(v_info_3467_);
return v___x_3469_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_3452_ = stack[0].m_obj;
lean_object* v_hoverPos_3453_ = stack[1].m_obj;
uint8_t v_includeStop_3454_ = stack[2].m_num;
lean_object* v_filter_3455_ = stack[3].m_obj;
lean_object* v_res_3475_;
v_res_3475_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(v_t_3452_, v_hoverPos_3453_, v_includeStop_3454_, v_filter_3455_);
stack->m_obj
 = v_res_3475_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1___boxed(lean_object* v_t_3476_, lean_object* v_hoverPos_3477_, lean_object* v_includeStop_3478_, lean_object* v_filter_3479_){
_start:
{
uint8_t v_includeStop_boxed_3480_; lean_object* v_res_3481_; 
v_includeStop_boxed_3480_ = lean_unbox(v_includeStop_3478_);
v_res_3481_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(v_t_3476_, v_hoverPos_3477_, v_includeStop_boxed_3480_, v_filter_3479_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f(lean_object* v_t_3483_, lean_object* v_hoverPos_3484_){
_start:
{
lean_object* v_filter_3485_; uint8_t v___x_3486_; lean_object* v___x_3487_; 
v_filter_3485_ = ((lean_object*)(l_Lean_Elab_InfoTree_termGoalAt_x3f___closed__0));
v___x_3486_ = 1;
v___x_3487_ = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Elab_InfoTree_termGoalAt_x3f_spec__1(v_t_3483_, v_hoverPos_3484_, v___x_3486_, v_filter_3485_);
return v___x_3487_;
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
