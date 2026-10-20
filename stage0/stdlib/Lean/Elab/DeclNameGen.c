// Lean compiler output
// Module: Lean.Elab.DeclNameGen
// Imports: public import Lean.Elab.Command import Init.Data.String.Modify import Init.Omega
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
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
uint8_t l_Lean_Expr_isSort(lean_object*);
lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
uint8_t l_Lean_Expr_isType(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkUnusedBaseName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withAutoBoundImplicit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "u"};
static const lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__1 = (const lean_object*)&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__1_value),LEAN_SCALAR_PTR_LITERAL(232, 178, 247, 241, 102, 42, 87, 174)}};
static const lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__2 = (const lean_object*)&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3;
static lean_once_cell_t l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4;
static lean_once_cell_t l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5;
static lean_once_cell_t l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0;
static lean_once_cell_t l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0 = (const lean_object*)&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0_value;
static const lean_string_object l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Forall"};
static const lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0 = (const lean_object*)&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0_value;
static const lean_string_object l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prop"};
static const lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__1 = (const lean_object*)&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__1_value;
static const lean_string_object l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Type"};
static const lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__2 = (const lean_object*)&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__2_value;
static const lean_string_object l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Sort"};
static const lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__3 = (const lean_object*)&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Of"};
static const lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit___closed__0 = (const lean_object*)&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix___closed__0 = (const lean_object*)&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0 = (const lean_object*)&l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__0 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__0_value;
static const lean_ctor_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__1 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__8_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__19_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_mkInstanceName___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "inst"};
static const lean_object* l_Lean_Elab_Command_mkInstanceName___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Command_mkInstanceName___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg(lean_object* v_e_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Expr_getAppFn(v_e_1_);
if (lean_obj_tag(v___x_10_) == 4)
{
lean_object* v_declName_11_; 
v_declName_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc(v_declName_11_);
lean_dec_ref_known(v___x_10_, 2);
if (lean_obj_tag(v_declName_11_) == 1)
{
lean_object* v_str_12_; lean_object* v___x_13_; lean_object* v_env_14_; lean_object* v___x_15_; 
v_str_12_ = lean_ctor_get(v_declName_11_, 1);
lean_inc_ref(v_str_12_);
v___x_13_ = lean_st_ref_get(v_a_2_);
v_env_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc_ref_n(v_env_14_, 2);
lean_dec(v___x_13_);
v___x_15_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_14_, v_declName_11_);
if (lean_obj_tag(v___x_15_) == 1)
{
lean_object* v_val_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_58_; 
v_val_16_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_58_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_58_ == 0)
{
v___x_18_ = v___x_15_;
v_isShared_19_ = v_isSharedCheck_58_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_val_16_);
lean_dec(v___x_15_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_58_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v_ctorName_20_; lean_object* v_numParams_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v_ctorName_20_ = lean_ctor_get(v_val_16_, 0);
lean_inc(v_ctorName_20_);
v_numParams_21_ = lean_ctor_get(v_val_16_, 1);
lean_inc(v_numParams_21_);
lean_dec(v_val_16_);
v___x_22_ = l_Lean_Expr_getAppNumArgs(v_e_1_);
v___x_23_ = lean_unsigned_to_nat(1u);
v___x_24_ = lean_nat_add(v_numParams_21_, v___x_23_);
lean_dec(v_numParams_21_);
v___x_25_ = lean_nat_dec_eq(v___x_22_, v___x_24_);
lean_dec(v___x_24_);
lean_dec(v___x_22_);
if (v___x_25_ == 0)
{
lean_object* v___x_26_; lean_object* v___x_28_; 
lean_dec(v_ctorName_20_);
lean_dec_ref(v_env_14_);
lean_dec_ref(v_str_12_);
v___x_26_ = lean_box(0);
if (v_isShared_19_ == 0)
{
lean_ctor_set_tag(v___x_18_, 0);
lean_ctor_set(v___x_18_, 0, v___x_26_);
v___x_28_ = v___x_18_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_26_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
else
{
uint8_t v___x_30_; lean_object* v___x_31_; 
lean_del_object(v___x_18_);
v___x_30_ = 0;
lean_inc_ref(v_env_14_);
v___x_31_ = l_Lean_Environment_find_x3f(v_env_14_, v_ctorName_20_, v___x_30_);
if (lean_obj_tag(v___x_31_) == 1)
{
lean_object* v_val_32_; 
v_val_32_ = lean_ctor_get(v___x_31_, 0);
lean_inc(v_val_32_);
lean_dec_ref_known(v___x_31_, 1);
if (lean_obj_tag(v_val_32_) == 6)
{
lean_object* v_val_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_57_; 
v_val_33_ = lean_ctor_get(v_val_32_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v_val_32_);
if (v_isSharedCheck_57_ == 0)
{
v___x_35_ = v_val_32_;
v_isShared_36_ = v_isSharedCheck_57_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_val_33_);
lean_dec(v_val_32_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_57_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v_induct_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v_induct_37_ = lean_ctor_get(v_val_33_, 1);
lean_inc(v_induct_37_);
lean_dec_ref(v_val_33_);
v___x_38_ = lean_box(0);
v___x_39_ = l_Lean_Name_str___override(v___x_38_, v_str_12_);
v___x_40_ = l_Lean_isSubobjectField_x3f(v_env_14_, v_induct_37_, v___x_39_);
if (lean_obj_tag(v___x_40_) == 0)
{
lean_object* v___x_41_; lean_object* v___x_43_; 
v___x_41_ = lean_box(0);
if (v_isShared_36_ == 0)
{
lean_ctor_set_tag(v___x_35_, 0);
lean_ctor_set(v___x_35_, 0, v___x_41_);
v___x_43_ = v___x_35_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_41_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
else
{
lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_55_; 
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_55_ == 0)
{
lean_object* v_unused_56_; 
v_unused_56_ = lean_ctor_get(v___x_40_, 0);
lean_dec(v_unused_56_);
v___x_46_ = v___x_40_;
v_isShared_47_ = v_isSharedCheck_55_;
goto v_resetjp_45_;
}
else
{
lean_dec(v___x_40_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_55_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_48_; lean_object* v___x_50_; 
v___x_48_ = l_Lean_Expr_appArg_x21(v_e_1_);
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 0, v___x_48_);
v___x_50_ = v___x_46_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_48_);
v___x_50_ = v_reuseFailAlloc_54_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
lean_object* v___x_52_; 
if (v_isShared_36_ == 0)
{
lean_ctor_set_tag(v___x_35_, 0);
lean_ctor_set(v___x_35_, 0, v___x_50_);
v___x_52_ = v___x_35_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_50_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
}
}
else
{
lean_dec(v_val_32_);
lean_dec_ref(v_env_14_);
lean_dec_ref(v_str_12_);
goto v___jp_7_;
}
}
else
{
lean_dec(v___x_31_);
lean_dec_ref(v_env_14_);
lean_dec_ref(v_str_12_);
goto v___jp_7_;
}
}
}
}
else
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec(v___x_15_);
lean_dec_ref(v_env_14_);
lean_dec_ref(v_str_12_);
v___x_59_ = lean_box(0);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
}
else
{
lean_dec(v_declName_11_);
goto v___jp_4_;
}
}
else
{
lean_dec_ref(v___x_10_);
goto v___jp_4_;
}
v___jp_4_:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_box(0);
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
v___jp_7_:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_box(0);
v___x_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg___boxed(lean_object* v_e_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg(v_e_61_, v_a_62_);
lean_dec(v_a_62_);
lean_dec_ref(v_e_61_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg(lean_object* v_e_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg(v_e_65_, v_a_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___boxed(lean_object* v_e_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg(v_e_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
lean_dec(v_a_76_);
lean_dec_ref(v_a_75_);
lean_dec(v_a_74_);
lean_dec_ref(v_a_73_);
lean_dec_ref(v_e_72_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___lam__0(lean_object* v_k_79_, lean_object* v___y_80_, lean_object* v_b_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v___x_87_; 
lean_inc(v___y_85_);
lean_inc_ref(v___y_84_);
lean_inc(v___y_83_);
lean_inc_ref(v___y_82_);
lean_inc(v___y_80_);
v___x_87_ = lean_apply_7(v_k_79_, v_b_81_, v___y_80_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, lean_box(0));
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___lam__0___boxed(lean_object* v_k_88_, lean_object* v___y_89_, lean_object* v_b_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___lam__0(v_k_88_, v___y_89_, v_b_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_89_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(lean_object* v_name_97_, uint8_t v_bi_98_, lean_object* v_type_99_, lean_object* v_k_100_, uint8_t v_kind_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v___f_108_; lean_object* v___x_109_; 
lean_inc(v___y_102_);
v___f_108_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_108_, 0, v_k_100_);
lean_closure_set(v___f_108_, 1, v___y_102_);
v___x_109_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_97_, v_bi_98_, v_type_99_, v___f_108_, v_kind_101_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
if (lean_obj_tag(v___x_109_) == 0)
{
return v___x_109_;
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_109_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___boxed(lean_object* v_name_118_, lean_object* v_bi_119_, lean_object* v_type_120_, lean_object* v_k_121_, lean_object* v_kind_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
uint8_t v_bi_boxed_129_; uint8_t v_kind_boxed_130_; lean_object* v_res_131_; 
v_bi_boxed_129_ = lean_unbox(v_bi_119_);
v_kind_boxed_130_ = lean_unbox(v_kind_122_);
v_res_131_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(v_name_118_, v_bi_boxed_129_, v_type_120_, v_k_121_, v_kind_boxed_130_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5(lean_object* v_00_u03b1_132_, lean_object* v_name_133_, uint8_t v_bi_134_, lean_object* v_type_135_, lean_object* v_k_136_, uint8_t v_kind_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(v_name_133_, v_bi_134_, v_type_135_, v_k_136_, v_kind_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___boxed(lean_object* v_00_u03b1_145_, lean_object* v_name_146_, lean_object* v_bi_147_, lean_object* v_type_148_, lean_object* v_k_149_, lean_object* v_kind_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
uint8_t v_bi_boxed_157_; uint8_t v_kind_boxed_158_; lean_object* v_res_159_; 
v_bi_boxed_157_ = lean_unbox(v_bi_147_);
v_kind_boxed_158_ = lean_unbox(v_kind_150_);
v_res_159_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5(v_00_u03b1_145_, v_name_146_, v_bi_boxed_157_, v_type_148_, v_k_149_, v_kind_boxed_158_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v___y_151_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(lean_object* v_msgData_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v___x_166_; lean_object* v_env_167_; uint8_t v___x_168_; lean_object* v_env_169_; lean_object* v___x_170_; lean_object* v_toCold_171_; lean_object* v_mctx_172_; lean_object* v_lctx_173_; lean_object* v_options_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_166_ = lean_st_ref_get(v___y_164_);
v_env_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc_ref(v_env_167_);
lean_dec(v___x_166_);
v___x_168_ = 0;
v_env_169_ = l_Lean_Environment_setRecordingDeps(v_env_167_, v___x_168_);
v___x_170_ = lean_st_ref_get(v___y_162_);
v_toCold_171_ = lean_ctor_get(v___y_163_, 0);
v_mctx_172_ = lean_ctor_get(v___x_170_, 0);
lean_inc_ref(v_mctx_172_);
lean_dec(v___x_170_);
v_lctx_173_ = lean_ctor_get(v___y_161_, 2);
v_options_174_ = lean_ctor_get(v_toCold_171_, 2);
lean_inc_ref(v_options_174_);
lean_inc_ref(v_lctx_173_);
v___x_175_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_175_, 0, v_env_169_);
lean_ctor_set(v___x_175_, 1, v_mctx_172_);
lean_ctor_set(v___x_175_, 2, v_lctx_173_);
lean_ctor_set(v___x_175_, 3, v_options_174_);
v___x_176_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v_msgData_160_);
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0___boxed(lean_object* v_msgData_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msgData_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(lean_object* v_msg_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v_ref_191_; lean_object* v___x_192_; lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_201_; 
v_ref_191_ = lean_ctor_get(v___y_188_, 2);
v___x_192_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msg_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
v_a_193_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_201_ == 0)
{
v___x_195_ = v___x_192_;
v_isShared_196_ = v_isSharedCheck_201_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_192_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_201_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_199_; 
lean_inc(v_ref_191_);
v___x_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_197_, 0, v_ref_191_);
lean_ctor_set(v___x_197_, 1, v_a_193_);
if (v_isShared_196_ == 0)
{
lean_ctor_set_tag(v___x_195_, 1);
lean_ctor_set(v___x_195_, 0, v___x_197_);
v___x_199_ = v___x_195_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_197_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg___boxed(lean_object* v_msg_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v_msg_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
return v_res_208_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(lean_object* v_a_209_, lean_object* v_x_210_){
_start:
{
if (lean_obj_tag(v_x_210_) == 0)
{
uint8_t v___x_211_; 
v___x_211_ = 0;
return v___x_211_;
}
else
{
lean_object* v_key_212_; lean_object* v_tail_213_; uint8_t v___x_214_; 
v_key_212_ = lean_ctor_get(v_x_210_, 0);
v_tail_213_ = lean_ctor_get(v_x_210_, 2);
v___x_214_ = lean_expr_eqv(v_key_212_, v_a_209_);
if (v___x_214_ == 0)
{
v_x_210_ = v_tail_213_;
goto _start;
}
else
{
return v___x_214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg___boxed(lean_object* v_a_216_, lean_object* v_x_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_216_, v_x_217_);
lean_dec(v_x_217_);
lean_dec_ref(v_a_216_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9___redArg(lean_object* v_x_220_, lean_object* v_x_221_){
_start:
{
if (lean_obj_tag(v_x_221_) == 0)
{
return v_x_220_;
}
else
{
lean_object* v_key_222_; lean_object* v_value_223_; lean_object* v_tail_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_247_; 
v_key_222_ = lean_ctor_get(v_x_221_, 0);
v_value_223_ = lean_ctor_get(v_x_221_, 1);
v_tail_224_ = lean_ctor_get(v_x_221_, 2);
v_isSharedCheck_247_ = !lean_is_exclusive(v_x_221_);
if (v_isSharedCheck_247_ == 0)
{
v___x_226_ = v_x_221_;
v_isShared_227_ = v_isSharedCheck_247_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_tail_224_);
lean_inc(v_value_223_);
lean_inc(v_key_222_);
lean_dec(v_x_221_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_247_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; uint64_t v___x_229_; uint64_t v___x_230_; uint64_t v___x_231_; uint64_t v_fold_232_; uint64_t v___x_233_; uint64_t v___x_234_; uint64_t v___x_235_; size_t v___x_236_; size_t v___x_237_; size_t v___x_238_; size_t v___x_239_; size_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_228_ = lean_array_get_size(v_x_220_);
v___x_229_ = l_Lean_Expr_hash(v_key_222_);
v___x_230_ = 32ULL;
v___x_231_ = lean_uint64_shift_right(v___x_229_, v___x_230_);
v_fold_232_ = lean_uint64_xor(v___x_229_, v___x_231_);
v___x_233_ = 16ULL;
v___x_234_ = lean_uint64_shift_right(v_fold_232_, v___x_233_);
v___x_235_ = lean_uint64_xor(v_fold_232_, v___x_234_);
v___x_236_ = lean_uint64_to_usize(v___x_235_);
v___x_237_ = lean_usize_of_nat(v___x_228_);
v___x_238_ = ((size_t)1ULL);
v___x_239_ = lean_usize_sub(v___x_237_, v___x_238_);
v___x_240_ = lean_usize_land(v___x_236_, v___x_239_);
v___x_241_ = lean_array_uget_borrowed(v_x_220_, v___x_240_);
lean_inc(v___x_241_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 2, v___x_241_);
v___x_243_ = v___x_226_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_key_222_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_value_223_);
lean_ctor_set(v_reuseFailAlloc_246_, 2, v___x_241_);
v___x_243_ = v_reuseFailAlloc_246_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_244_; 
v___x_244_ = lean_array_uset(v_x_220_, v___x_240_, v___x_243_);
v_x_220_ = v___x_244_;
v_x_221_ = v_tail_224_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6___redArg(lean_object* v_i_248_, lean_object* v_source_249_, lean_object* v_target_250_){
_start:
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = lean_array_get_size(v_source_249_);
v___x_252_ = lean_nat_dec_lt(v_i_248_, v___x_251_);
if (v___x_252_ == 0)
{
lean_dec_ref(v_source_249_);
lean_dec(v_i_248_);
return v_target_250_;
}
else
{
lean_object* v_es_253_; lean_object* v___x_254_; lean_object* v_source_255_; lean_object* v_target_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_es_253_ = lean_array_fget(v_source_249_, v_i_248_);
v___x_254_ = lean_box(0);
v_source_255_ = lean_array_fset(v_source_249_, v_i_248_, v___x_254_);
v_target_256_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9___redArg(v_target_250_, v_es_253_);
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = lean_nat_add(v_i_248_, v___x_257_);
lean_dec(v_i_248_);
v_i_248_ = v___x_258_;
v_source_249_ = v_source_255_;
v_target_250_ = v_target_256_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(lean_object* v_data_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v_nbuckets_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_261_ = lean_array_get_size(v_data_260_);
v___x_262_ = lean_unsigned_to_nat(2u);
v_nbuckets_263_ = lean_nat_mul(v___x_261_, v___x_262_);
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = lean_box(0);
v___x_266_ = lean_mk_array(v_nbuckets_263_, v___x_265_);
v___x_267_ = lean_array_propagate_mark(v_data_260_, v___x_266_);
v___x_268_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6___redArg(v___x_264_, v_data_260_, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(lean_object* v_a_269_, lean_object* v_b_270_, lean_object* v_x_271_){
_start:
{
if (lean_obj_tag(v_x_271_) == 0)
{
lean_dec(v_b_270_);
lean_dec_ref(v_a_269_);
return v_x_271_;
}
else
{
lean_object* v_key_272_; lean_object* v_value_273_; lean_object* v_tail_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_286_; 
v_key_272_ = lean_ctor_get(v_x_271_, 0);
v_value_273_ = lean_ctor_get(v_x_271_, 1);
v_tail_274_ = lean_ctor_get(v_x_271_, 2);
v_isSharedCheck_286_ = !lean_is_exclusive(v_x_271_);
if (v_isSharedCheck_286_ == 0)
{
v___x_276_ = v_x_271_;
v_isShared_277_ = v_isSharedCheck_286_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_tail_274_);
lean_inc(v_value_273_);
lean_inc(v_key_272_);
lean_dec(v_x_271_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_286_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
uint8_t v___x_278_; 
v___x_278_ = lean_expr_eqv(v_key_272_, v_a_269_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_279_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(v_a_269_, v_b_270_, v_tail_274_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 2, v___x_279_);
v___x_281_ = v___x_276_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_key_272_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_value_273_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
else
{
lean_object* v___x_284_; 
lean_dec(v_value_273_);
lean_dec(v_key_272_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 1, v_b_270_);
lean_ctor_set(v___x_276_, 0, v_a_269_);
v___x_284_ = v___x_276_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_269_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_b_270_);
lean_ctor_set(v_reuseFailAlloc_285_, 2, v_tail_274_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(lean_object* v_m_287_, lean_object* v_a_288_, lean_object* v_b_289_){
_start:
{
lean_object* v_size_290_; lean_object* v_buckets_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_334_; 
v_size_290_ = lean_ctor_get(v_m_287_, 0);
v_buckets_291_ = lean_ctor_get(v_m_287_, 1);
v_isSharedCheck_334_ = !lean_is_exclusive(v_m_287_);
if (v_isSharedCheck_334_ == 0)
{
v___x_293_ = v_m_287_;
v_isShared_294_ = v_isSharedCheck_334_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_buckets_291_);
lean_inc(v_size_290_);
lean_dec(v_m_287_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_334_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; uint64_t v___x_296_; uint64_t v___x_297_; uint64_t v___x_298_; uint64_t v_fold_299_; uint64_t v___x_300_; uint64_t v___x_301_; uint64_t v___x_302_; size_t v___x_303_; size_t v___x_304_; size_t v___x_305_; size_t v___x_306_; size_t v___x_307_; lean_object* v_bkt_308_; uint8_t v___x_309_; 
v___x_295_ = lean_array_get_size(v_buckets_291_);
v___x_296_ = l_Lean_Expr_hash(v_a_288_);
v___x_297_ = 32ULL;
v___x_298_ = lean_uint64_shift_right(v___x_296_, v___x_297_);
v_fold_299_ = lean_uint64_xor(v___x_296_, v___x_298_);
v___x_300_ = 16ULL;
v___x_301_ = lean_uint64_shift_right(v_fold_299_, v___x_300_);
v___x_302_ = lean_uint64_xor(v_fold_299_, v___x_301_);
v___x_303_ = lean_uint64_to_usize(v___x_302_);
v___x_304_ = lean_usize_of_nat(v___x_295_);
v___x_305_ = ((size_t)1ULL);
v___x_306_ = lean_usize_sub(v___x_304_, v___x_305_);
v___x_307_ = lean_usize_land(v___x_303_, v___x_306_);
v_bkt_308_ = lean_array_uget_borrowed(v_buckets_291_, v___x_307_);
v___x_309_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_288_, v_bkt_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v_size_x27_311_; lean_object* v___x_312_; lean_object* v_buckets_x27_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_310_ = lean_unsigned_to_nat(1u);
v_size_x27_311_ = lean_nat_add(v_size_290_, v___x_310_);
lean_dec(v_size_290_);
lean_inc(v_bkt_308_);
v___x_312_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_312_, 0, v_a_288_);
lean_ctor_set(v___x_312_, 1, v_b_289_);
lean_ctor_set(v___x_312_, 2, v_bkt_308_);
v_buckets_x27_313_ = lean_array_uset(v_buckets_291_, v___x_307_, v___x_312_);
v___x_314_ = lean_unsigned_to_nat(4u);
v___x_315_ = lean_nat_mul(v_size_x27_311_, v___x_314_);
v___x_316_ = lean_unsigned_to_nat(3u);
v___x_317_ = lean_nat_div(v___x_315_, v___x_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_array_get_size(v_buckets_x27_313_);
v___x_319_ = lean_nat_dec_le(v___x_317_, v___x_318_);
lean_dec(v___x_317_);
if (v___x_319_ == 0)
{
lean_object* v_val_320_; lean_object* v___x_322_; 
v_val_320_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(v_buckets_x27_313_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v_val_320_);
lean_ctor_set(v___x_293_, 0, v_size_x27_311_);
v___x_322_ = v___x_293_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_size_x27_311_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_val_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
else
{
lean_object* v___x_325_; 
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v_buckets_x27_313_);
lean_ctor_set(v___x_293_, 0, v_size_x27_311_);
v___x_325_ = v___x_293_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_size_x27_311_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_buckets_x27_313_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
else
{
lean_object* v___x_327_; lean_object* v_buckets_x27_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_332_; 
lean_inc(v_bkt_308_);
v___x_327_ = lean_box(0);
v_buckets_x27_328_ = lean_array_uset(v_buckets_291_, v___x_307_, v___x_327_);
v___x_329_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(v_a_288_, v_b_289_, v_bkt_308_);
v___x_330_ = lean_array_uset(v_buckets_x27_328_, v___x_307_, v___x_329_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v___x_330_);
v___x_332_ = v___x_293_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_size_290_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(lean_object* v_a_335_, lean_object* v_x_336_){
_start:
{
if (lean_obj_tag(v_x_336_) == 0)
{
lean_object* v___x_337_; 
v___x_337_ = lean_box(0);
return v___x_337_;
}
else
{
lean_object* v_key_338_; lean_object* v_value_339_; lean_object* v_tail_340_; uint8_t v___x_341_; 
v_key_338_ = lean_ctor_get(v_x_336_, 0);
v_value_339_ = lean_ctor_get(v_x_336_, 1);
v_tail_340_ = lean_ctor_get(v_x_336_, 2);
v___x_341_ = lean_expr_eqv(v_key_338_, v_a_335_);
if (v___x_341_ == 0)
{
v_x_336_ = v_tail_340_;
goto _start;
}
else
{
lean_object* v___x_343_; 
lean_inc(v_value_339_);
v___x_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_343_, 0, v_value_339_);
return v___x_343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg___boxed(lean_object* v_a_344_, lean_object* v_x_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(v_a_344_, v_x_345_);
lean_dec(v_x_345_);
lean_dec_ref(v_a_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(lean_object* v_m_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_buckets_349_; lean_object* v___x_350_; uint64_t v___x_351_; uint64_t v___x_352_; uint64_t v___x_353_; uint64_t v_fold_354_; uint64_t v___x_355_; uint64_t v___x_356_; uint64_t v___x_357_; size_t v___x_358_; size_t v___x_359_; size_t v___x_360_; size_t v___x_361_; size_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_buckets_349_ = lean_ctor_get(v_m_347_, 1);
v___x_350_ = lean_array_get_size(v_buckets_349_);
v___x_351_ = l_Lean_Expr_hash(v_a_348_);
v___x_352_ = 32ULL;
v___x_353_ = lean_uint64_shift_right(v___x_351_, v___x_352_);
v_fold_354_ = lean_uint64_xor(v___x_351_, v___x_353_);
v___x_355_ = 16ULL;
v___x_356_ = lean_uint64_shift_right(v_fold_354_, v___x_355_);
v___x_357_ = lean_uint64_xor(v_fold_354_, v___x_356_);
v___x_358_ = lean_uint64_to_usize(v___x_357_);
v___x_359_ = lean_usize_of_nat(v___x_350_);
v___x_360_ = ((size_t)1ULL);
v___x_361_ = lean_usize_sub(v___x_359_, v___x_360_);
v___x_362_ = lean_usize_land(v___x_358_, v___x_361_);
v___x_363_ = lean_array_uget_borrowed(v_buckets_349_, v___x_362_);
v___x_364_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(v_a_348_, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg___boxed(lean_object* v_m_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v_m_365_, v_a_366_);
lean_dec_ref(v_a_366_);
lean_dec_ref(v_m_365_);
return v_res_367_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0(void){
_start:
{
lean_object* v___x_368_; lean_object* v_dummy_369_; 
v___x_368_ = lean_box(0);
v_dummy_369_ = l_Lean_Expr_sort___override(v___x_368_);
return v_dummy_369_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__0));
v___x_372_ = l_Lean_stringToMessageData(v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(lean_object* v_args_373_, lean_object* v_a_374_, lean_object* v_snd_375_, lean_object* v_____r_376_, lean_object* v_fty_377_, lean_object* v_j_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
if (lean_obj_tag(v_fty_377_) == 7)
{
lean_object* v_body_385_; uint8_t v_binderInfo_386_; lean_object* v___x_392_; uint8_t v___x_436_; 
v_body_385_ = lean_ctor_get(v_fty_377_, 2);
lean_inc_ref(v_body_385_);
v_binderInfo_386_ = lean_ctor_get_uint8(v_fty_377_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_fty_377_, 3);
v___x_392_ = lean_array_fget_borrowed(v_args_373_, v_a_374_);
v___x_436_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_386_);
if (v___x_436_ == 0)
{
uint8_t v___x_437_; 
v___x_437_ = l_Lean_Expr_isSort(v___x_392_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; 
lean_inc(v___x_392_);
v___x_438_ = l_Lean_Meta_isTypeFormer(v___x_392_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; uint8_t v___x_440_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_438_, 1);
v___x_440_ = lean_unbox(v_a_439_);
lean_dec(v_a_439_);
if (v___x_440_ == 0)
{
goto v___jp_387_;
}
else
{
goto v___jp_393_;
}
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
lean_dec_ref(v_body_385_);
lean_dec(v_snd_375_);
v_a_441_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_438_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_438_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
else
{
goto v___jp_387_;
}
}
else
{
goto v___jp_393_;
}
v___jp_387_:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
lean_inc(v_j_378_);
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v_j_378_);
lean_ctor_set(v___x_388_, 1, v_snd_375_);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v_body_385_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
v___jp_393_:
{
lean_object* v___x_394_; 
lean_inc(v___x_392_);
v___x_394_ = l_Lean_Meta_isProof(v___x_392_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_427_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_427_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_427_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_427_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
uint8_t v___x_399_; 
v___x_399_ = lean_unbox(v_a_395_);
lean_dec(v_a_395_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; 
lean_del_object(v___x_397_);
lean_inc(v___x_392_);
v___x_400_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_392_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_412_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_412_ == 0)
{
v___x_403_ = v___x_400_;
v_isShared_404_ = v_isSharedCheck_412_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_400_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_412_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_405_ = l_Lean_Expr_app___override(v_snd_375_, v_a_401_);
lean_inc(v_j_378_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v_j_378_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v_body_385_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_408_);
v___x_410_ = v___x_403_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec_ref(v_body_385_);
lean_dec(v_snd_375_);
v_a_413_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_400_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_400_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
lean_inc(v_j_378_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v_j_378_);
lean_ctor_set(v___x_421_, 1, v_snd_375_);
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v_body_385_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_423_);
v___x_425_ = v___x_397_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec_ref(v_body_385_);
lean_dec(v_snd_375_);
v_a_428_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_394_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_394_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
else
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1);
v___x_450_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v___x_449_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_460_; 
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_460_ == 0)
{
lean_object* v_unused_461_; 
v_unused_461_ = lean_ctor_get(v___x_450_, 0);
lean_dec(v_unused_461_);
v___x_452_ = v___x_450_;
v_isShared_453_ = v_isSharedCheck_460_;
goto v_resetjp_451_;
}
else
{
lean_dec(v___x_450_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_460_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
lean_inc(v_j_378_);
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v_j_378_);
lean_ctor_set(v___x_454_, 1, v_snd_375_);
v___x_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_455_, 0, v_fty_377_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_456_);
v___x_458_ = v___x_452_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
lean_dec_ref(v_fty_377_);
lean_dec(v_snd_375_);
v_a_462_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_450_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_450_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(lean_object* v_upperBound_470_, lean_object* v_args_471_, lean_object* v_a_472_, lean_object* v_b_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___y_481_; uint8_t v___x_503_; 
v___x_503_ = lean_nat_dec_lt(v_a_472_, v_upperBound_470_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; 
lean_dec(v_a_472_);
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v_b_473_);
return v___x_504_;
}
else
{
lean_object* v_snd_505_; lean_object* v_fst_506_; lean_object* v_fst_507_; lean_object* v_snd_508_; lean_object* v___y_510_; uint8_t v___x_522_; 
v_snd_505_ = lean_ctor_get(v_b_473_, 1);
lean_inc(v_snd_505_);
v_fst_506_ = lean_ctor_get(v_b_473_, 0);
lean_inc(v_fst_506_);
lean_dec_ref(v_b_473_);
v_fst_507_ = lean_ctor_get(v_snd_505_, 0);
lean_inc(v_fst_507_);
v_snd_508_ = lean_ctor_get(v_snd_505_, 1);
lean_inc(v_snd_508_);
lean_dec(v_snd_505_);
v___x_522_ = l_Lean_Expr_isForall(v_fst_506_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; uint8_t v_transparency_524_; uint8_t v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_523_ = l_Lean_Meta_Context_config(v___y_475_);
v_transparency_524_ = lean_ctor_get_uint8(v___x_523_, 9);
lean_dec_ref(v___x_523_);
v___x_525_ = 0;
v___x_526_ = lean_expr_instantiate_rev_range(v_fst_506_, v_fst_507_, v_a_472_, v_args_471_);
lean_dec(v_fst_507_);
lean_dec(v_fst_506_);
v___x_527_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_524_, v___x_525_);
if (v___x_527_ == 0)
{
lean_object* v_keyedConfig_528_; uint8_t v_trackZetaDelta_529_; lean_object* v_zetaDeltaSet_530_; lean_object* v_lctx_531_; lean_object* v_localInstances_532_; lean_object* v_defEqCtx_x3f_533_; lean_object* v_synthPendingDepth_534_; lean_object* v_customCanUnfoldPredicate_x3f_535_; uint8_t v_univApprox_536_; uint8_t v_inTypeClassResolution_537_; uint8_t v_cacheInferType_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_keyedConfig_528_ = lean_ctor_get(v___y_475_, 0);
v_trackZetaDelta_529_ = lean_ctor_get_uint8(v___y_475_, sizeof(void*)*7);
v_zetaDeltaSet_530_ = lean_ctor_get(v___y_475_, 1);
v_lctx_531_ = lean_ctor_get(v___y_475_, 2);
v_localInstances_532_ = lean_ctor_get(v___y_475_, 3);
v_defEqCtx_x3f_533_ = lean_ctor_get(v___y_475_, 4);
v_synthPendingDepth_534_ = lean_ctor_get(v___y_475_, 5);
v_customCanUnfoldPredicate_x3f_535_ = lean_ctor_get(v___y_475_, 6);
v_univApprox_536_ = lean_ctor_get_uint8(v___y_475_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_537_ = lean_ctor_get_uint8(v___y_475_, sizeof(void*)*7 + 2);
v_cacheInferType_538_ = lean_ctor_get_uint8(v___y_475_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_528_);
v___x_539_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_525_, v_keyedConfig_528_);
lean_inc(v_customCanUnfoldPredicate_x3f_535_);
lean_inc(v_synthPendingDepth_534_);
lean_inc(v_defEqCtx_x3f_533_);
lean_inc_ref(v_localInstances_532_);
lean_inc_ref(v_lctx_531_);
lean_inc(v_zetaDeltaSet_530_);
v___x_540_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_540_, 0, v___x_539_);
lean_ctor_set(v___x_540_, 1, v_zetaDeltaSet_530_);
lean_ctor_set(v___x_540_, 2, v_lctx_531_);
lean_ctor_set(v___x_540_, 3, v_localInstances_532_);
lean_ctor_set(v___x_540_, 4, v_defEqCtx_x3f_533_);
lean_ctor_set(v___x_540_, 5, v_synthPendingDepth_534_);
lean_ctor_set(v___x_540_, 6, v_customCanUnfoldPredicate_x3f_535_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*7, v_trackZetaDelta_529_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*7 + 1, v_univApprox_536_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*7 + 2, v_inTypeClassResolution_537_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*7 + 3, v_cacheInferType_538_);
lean_inc(v___y_478_);
lean_inc_ref(v___y_477_);
lean_inc(v___y_476_);
v___x_541_ = lean_whnf(v___x_526_, v___x_540_, v___y_476_, v___y_477_, v___y_478_);
v___y_510_ = v___x_541_;
goto v___jp_509_;
}
else
{
lean_object* v___x_542_; 
lean_inc(v___y_478_);
lean_inc_ref(v___y_477_);
lean_inc(v___y_476_);
lean_inc_ref(v___y_475_);
v___x_542_ = lean_whnf(v___x_526_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
v___y_510_ = v___x_542_;
goto v___jp_509_;
}
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_box(0);
v___x_544_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_args_471_, v_a_472_, v_snd_508_, v___x_543_, v_fst_506_, v_fst_507_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
lean_dec(v_fst_507_);
v___y_481_ = v___x_544_;
goto v___jp_480_;
}
v___jp_509_:
{
if (lean_obj_tag(v___y_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_a_511_ = lean_ctor_get(v___y_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref_known(v___y_510_, 1);
v___x_512_ = lean_box(0);
v___x_513_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_args_471_, v_a_472_, v_snd_508_, v___x_512_, v_a_511_, v_a_472_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
v___y_481_ = v___x_513_;
goto v___jp_480_;
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
lean_dec(v_snd_508_);
lean_dec(v_a_472_);
v_a_514_ = lean_ctor_get(v___y_510_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___y_510_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___y_510_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___y_510_);
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
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
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
}
}
v___jp_480_:
{
if (lean_obj_tag(v___y_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_494_; 
v_a_482_ = lean_ctor_get(v___y_481_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___y_481_);
if (v_isSharedCheck_494_ == 0)
{
v___x_484_ = v___y_481_;
v_isShared_485_ = v_isSharedCheck_494_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___y_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_494_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
if (lean_obj_tag(v_a_482_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_488_; 
lean_dec(v_a_472_);
v_a_486_ = lean_ctor_get(v_a_482_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v_a_482_, 1);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v_a_486_);
v___x_488_ = v___x_484_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
else
{
lean_object* v_a_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
lean_del_object(v___x_484_);
v_a_490_ = lean_ctor_get(v_a_482_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v_a_482_, 1);
v___x_491_ = lean_unsigned_to_nat(1u);
v___x_492_ = lean_nat_add(v_a_472_, v___x_491_);
lean_dec(v_a_472_);
v_a_472_ = v___x_492_;
v_b_473_ = v_a_490_;
goto _start;
}
}
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_dec(v_a_472_);
v_a_495_ = lean_ctor_get(v___y_481_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___y_481_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___y_481_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___y_481_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(lean_object* v_x_545_, lean_object* v_x_546_, lean_object* v_x_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
if (lean_obj_tag(v_x_545_) == 5)
{
lean_object* v_fn_554_; lean_object* v_arg_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_fn_554_ = lean_ctor_get(v_x_545_, 0);
lean_inc_ref(v_fn_554_);
v_arg_555_ = lean_ctor_get(v_x_545_, 1);
lean_inc_ref(v_arg_555_);
lean_dec_ref_known(v_x_545_, 2);
v___x_556_ = lean_array_set(v_x_546_, v_x_547_, v_arg_555_);
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = lean_nat_sub(v_x_547_, v___x_557_);
lean_dec(v_x_547_);
v_x_545_ = v_fn_554_;
v_x_546_ = v___x_556_;
v_x_547_ = v___x_558_;
goto _start;
}
else
{
lean_object* v___x_560_; 
lean_dec(v_x_547_);
lean_inc(v___y_552_);
lean_inc_ref(v___y_551_);
lean_inc(v___y_550_);
lean_inc_ref(v___y_549_);
lean_inc_ref(v_x_545_);
v___x_560_ = lean_infer_type(v_x_545_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_561_);
lean_dec_ref_known(v___x_560_, 1);
v___x_562_ = lean_unsigned_to_nat(0u);
v___x_563_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_x_545_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref_known(v___x_563_, 1);
v___x_565_ = lean_array_get_size(v_x_546_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_562_);
lean_ctor_set(v___x_566_, 1, v_a_564_);
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v_a_561_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v___x_565_, v_x_546_, v___x_562_, v___x_567_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec_ref(v_x_546_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_578_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_578_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_578_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_578_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v_snd_573_; lean_object* v_snd_574_; lean_object* v___x_576_; 
v_snd_573_ = lean_ctor_get(v_a_569_, 1);
lean_inc(v_snd_573_);
lean_dec(v_a_569_);
v_snd_574_ = lean_ctor_get(v_snd_573_, 1);
lean_inc(v_snd_574_);
lean_dec(v_snd_573_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v_snd_574_);
v___x_576_ = v___x_571_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_snd_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
v_a_579_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_568_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_568_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
else
{
lean_dec(v_a_561_);
lean_dec_ref(v_x_546_);
return v___x_563_;
}
}
else
{
lean_dec_ref(v_x_546_);
lean_dec_ref(v_x_545_);
return v___x_560_;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = l_Lean_Expr_bvar___override(v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0(lean_object* v_body_589_, lean_object* v_binderName_590_, uint8_t v_binderInfo_591_, lean_object* v_binderType_592_, lean_object* v_arg_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_ty_x27_601_; uint8_t v___x_613_; 
v___x_613_ = l_Lean_Expr_hasLooseBVars(v_body_589_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; 
v___x_614_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_binderType_592_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref_known(v___x_614_, 1);
v_ty_x27_601_ = v_a_615_;
goto v___jp_600_;
}
else
{
lean_dec(v_binderName_590_);
return v___x_614_;
}
}
else
{
lean_object* v___x_616_; 
lean_dec_ref(v_binderType_592_);
v___x_616_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0);
v_ty_x27_601_ = v___x_616_;
goto v___jp_600_;
}
v___jp_600_:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_expr_instantiate1(v_body_589_, v_arg_593_);
v___x_603_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_602_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_612_; 
v_a_604_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_612_ == 0)
{
v___x_606_ = v___x_603_;
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_603_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_608_ = l_Lean_Expr_forallE___override(v_binderName_590_, v_ty_x27_601_, v_a_604_, v_binderInfo_591_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_608_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
else
{
lean_dec_ref(v_ty_x27_601_);
lean_dec(v_binderName_590_);
return v___x_603_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___boxed(lean_object* v_body_617_, lean_object* v_binderName_618_, lean_object* v_binderInfo_619_, lean_object* v_binderType_620_, lean_object* v_arg_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
uint8_t v_binderInfo_15902__boxed_628_; lean_object* v_res_629_; 
v_binderInfo_15902__boxed_628_ = lean_unbox(v_binderInfo_619_);
v_res_629_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0(v_body_617_, v_binderName_618_, v_binderInfo_15902__boxed_628_, v_binderType_620_, v_arg_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v_arg_621_);
lean_dec_ref(v_body_617_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1___boxed(lean_object* v_body_630_, lean_object* v_arg_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1(v_body_630_, v_arg_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v_arg_631_);
lean_dec_ref(v_body_630_);
return v_res_638_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__2));
v___x_643_ = l_Lean_Level_param___override(v___x_642_);
return v___x_643_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3);
v___x_645_ = l_Lean_Expr_sort___override(v___x_644_);
return v___x_645_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_box(0);
v___x_647_ = l_Lean_Level_succ___override(v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5);
v___x_649_ = l_Lean_Expr_sort___override(v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(lean_object* v_e_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_a_658_; lean_object* v___y_664_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_st_ref_get(v_a_651_);
v___x_667_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v___x_666_, v_e_650_);
lean_dec(v___x_666_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v___x_668_; 
lean_inc_ref(v_e_650_);
v___x_668_ = l_Lean_Meta_isProof(v_e_650_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; uint8_t v___x_670_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
v___x_670_ = lean_unbox(v_a_669_);
lean_dec(v_a_669_);
if (v___x_670_ == 0)
{
switch(lean_obj_tag(v_e_650_))
{
case 5:
{
lean_object* v___x_671_; 
v___x_671_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg(v_e_650_, v_a_655_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_671_, 1);
if (lean_obj_tag(v_a_672_) == 1)
{
lean_object* v_val_673_; lean_object* v___x_674_; 
v_val_673_ = lean_ctor_get(v_a_672_, 0);
lean_inc(v_val_673_);
lean_dec_ref_known(v_a_672_, 1);
v___x_674_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_val_673_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
v___y_664_ = v___x_674_;
goto v___jp_663_;
}
else
{
lean_object* v_dummy_675_; lean_object* v_nargs_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
lean_dec(v_a_672_);
v_dummy_675_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0);
v_nargs_676_ = l_Lean_Expr_getAppNumArgs(v_e_650_);
lean_inc(v_nargs_676_);
v___x_677_ = lean_mk_array(v_nargs_676_, v_dummy_675_);
v___x_678_ = lean_unsigned_to_nat(1u);
v___x_679_ = lean_nat_sub(v_nargs_676_, v___x_678_);
lean_dec(v_nargs_676_);
lean_inc_ref(v_e_650_);
v___x_680_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(v_e_650_, v___x_677_, v___x_679_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
v___y_664_ = v___x_680_;
goto v___jp_663_;
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_dec_ref_known(v_e_650_, 2);
v_a_681_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_671_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_671_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
case 7:
{
lean_object* v_binderName_689_; lean_object* v_binderType_690_; lean_object* v_body_691_; uint8_t v_binderInfo_692_; lean_object* v___x_693_; lean_object* v___f_694_; uint8_t v___x_695_; lean_object* v___x_696_; 
v_binderName_689_ = lean_ctor_get(v_e_650_, 0);
v_binderType_690_ = lean_ctor_get(v_e_650_, 1);
v_body_691_ = lean_ctor_get(v_e_650_, 2);
v_binderInfo_692_ = lean_ctor_get_uint8(v_e_650_, sizeof(void*)*3 + 8);
v___x_693_ = lean_box(v_binderInfo_692_);
lean_inc_ref_n(v_binderType_690_, 2);
lean_inc_n(v_binderName_689_, 2);
lean_inc_ref(v_body_691_);
v___f_694_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___boxed), 11, 4);
lean_closure_set(v___f_694_, 0, v_body_691_);
lean_closure_set(v___f_694_, 1, v_binderName_689_);
lean_closure_set(v___f_694_, 2, v___x_693_);
lean_closure_set(v___f_694_, 3, v_binderType_690_);
v___x_695_ = 0;
v___x_696_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(v_binderName_689_, v_binderInfo_692_, v_binderType_690_, v___f_694_, v___x_695_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
v___y_664_ = v___x_696_;
goto v___jp_663_;
}
case 6:
{
lean_object* v_binderName_697_; lean_object* v_binderType_698_; lean_object* v_body_699_; uint8_t v_binderInfo_700_; lean_object* v___x_701_; 
v_binderName_697_ = lean_ctor_get(v_e_650_, 0);
v_binderType_698_ = lean_ctor_get(v_e_650_, 1);
v_body_699_ = lean_ctor_get(v_e_650_, 2);
v_binderInfo_700_ = lean_ctor_get_uint8(v_e_650_, sizeof(void*)*3 + 8);
lean_inc_ref(v_e_650_);
v___x_701_ = l_Lean_Expr_etaExpandedStrict_x3f(v_e_650_);
if (lean_obj_tag(v___x_701_) == 1)
{
lean_object* v_val_702_; lean_object* v___x_703_; 
v_val_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_val_702_);
lean_dec_ref_known(v___x_701_, 1);
v___x_703_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_val_702_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
v___y_664_ = v___x_703_;
goto v___jp_663_;
}
else
{
lean_object* v___f_704_; uint8_t v___x_705_; lean_object* v___x_706_; 
lean_dec(v___x_701_);
lean_inc_ref(v_body_699_);
v___f_704_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1___boxed), 8, 1);
lean_closure_set(v___f_704_, 0, v_body_699_);
v___x_705_ = 0;
lean_inc_ref(v_binderType_698_);
lean_inc(v_binderName_697_);
v___x_706_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(v_binderName_697_, v_binderInfo_700_, v_binderType_698_, v___f_704_, v___x_705_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
v___y_664_ = v___x_706_;
goto v___jp_663_;
}
}
case 8:
{
lean_object* v_value_707_; lean_object* v_body_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v_value_707_ = lean_ctor_get(v_e_650_, 2);
v_body_708_ = lean_ctor_get(v_e_650_, 3);
v___x_709_ = lean_expr_instantiate1(v_body_708_, v_value_707_);
v___x_710_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_709_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
v___y_664_ = v___x_710_;
goto v___jp_663_;
}
case 3:
{
uint8_t v___x_711_; 
v___x_711_ = l_Lean_Expr_isProp(v_e_650_);
if (v___x_711_ == 0)
{
uint8_t v___x_712_; 
v___x_712_ = l_Lean_Expr_isType(v_e_650_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
v___x_713_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4);
v_a_658_ = v___x_713_;
goto v___jp_657_;
}
else
{
lean_object* v___x_714_; 
v___x_714_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6);
v_a_658_ = v___x_714_;
goto v___jp_657_;
}
}
else
{
lean_object* v___x_715_; 
v___x_715_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0);
v_a_658_ = v___x_715_;
goto v___jp_657_;
}
}
case 4:
{
lean_object* v_declName_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_declName_716_ = lean_ctor_get(v_e_650_, 0);
v___x_717_ = lean_box(0);
lean_inc(v_declName_716_);
v___x_718_ = l_Lean_Expr_const___override(v_declName_716_, v___x_717_);
v_a_658_ = v___x_718_;
goto v___jp_657_;
}
case 10:
{
lean_object* v_expr_719_; lean_object* v___x_720_; 
v_expr_719_ = lean_ctor_get(v_e_650_, 1);
lean_inc_ref(v_expr_719_);
v___x_720_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_expr_719_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
v___y_664_ = v___x_720_;
goto v___jp_663_;
}
default: 
{
lean_object* v___x_721_; 
v___x_721_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0);
v_a_658_ = v___x_721_;
goto v___jp_657_;
}
}
}
else
{
lean_object* v___x_722_; 
v___x_722_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0);
v_a_658_ = v___x_722_;
goto v___jp_657_;
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec_ref(v_e_650_);
v_a_723_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_668_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_668_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
else
{
lean_object* v_val_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec_ref(v_e_650_);
v_val_731_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_667_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_val_731_);
lean_dec(v___x_667_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 0);
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_val_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
v___jp_657_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_659_ = lean_st_ref_take(v_a_651_);
lean_inc_ref(v_a_658_);
v___x_660_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v___x_659_, v_e_650_, v_a_658_);
v___x_661_ = lean_st_ref_put(v_a_651_, v___x_660_);
v___x_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_662_, 0, v_a_658_);
return v___x_662_;
}
v___jp_663_:
{
if (lean_obj_tag(v___y_664_) == 0)
{
lean_object* v_a_665_; 
v_a_665_ = lean_ctor_get(v___y_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref_known(v___y_664_, 1);
v_a_658_ = v_a_665_;
goto v___jp_657_;
}
else
{
lean_dec_ref(v_e_650_);
return v___y_664_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1(lean_object* v_body_739_, lean_object* v_arg_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_expr_instantiate1(v_body_739_, v_arg_740_);
v___x_748_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_747_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4___boxed(lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v_x_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(v_x_749_, v_x_750_, v_x_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___boxed(lean_object* v_upperBound_759_, lean_object* v_args_760_, lean_object* v_a_761_, lean_object* v_b_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v_upperBound_759_, v_args_760_, v_a_761_, v_b_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v_args_760_);
lean_dec(v_upperBound_759_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___boxed(lean_object* v_args_770_, lean_object* v_a_771_, lean_object* v_snd_772_, lean_object* v_____r_773_, lean_object* v_fty_774_, lean_object* v_j_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_args_770_, v_a_771_, v_snd_772_, v_____r_773_, v_fty_774_, v_j_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec(v_j_775_);
lean_dec(v_a_771_);
lean_dec_ref(v_args_770_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___boxed(lean_object* v_e_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_e_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0(lean_object* v_00_u03b1_791_, lean_object* v_msg_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v_msg_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___boxed(lean_object* v_00_u03b1_799_, lean_object* v_msg_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0(v_00_u03b1_799_, v_msg_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1(lean_object* v_upperBound_807_, lean_object* v_args_808_, lean_object* v_inst_809_, lean_object* v_R_810_, lean_object* v_a_811_, lean_object* v_b_812_, lean_object* v_c_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v_upperBound_807_, v_args_808_, v_a_811_, v_b_812_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___boxed(lean_object* v_upperBound_821_, lean_object* v_args_822_, lean_object* v_inst_823_, lean_object* v_R_824_, lean_object* v_a_825_, lean_object* v_b_826_, lean_object* v_c_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1(v_upperBound_821_, v_args_822_, v_inst_823_, v_R_824_, v_a_825_, v_b_826_, v_c_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v_args_822_);
lean_dec(v_upperBound_821_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2(lean_object* v_00_u03b2_835_, lean_object* v_m_836_, lean_object* v_a_837_, lean_object* v_b_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v_m_836_, v_a_837_, v_b_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3(lean_object* v_00_u03b2_840_, lean_object* v_m_841_, lean_object* v_a_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v_m_841_, v_a_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___boxed(lean_object* v_00_u03b2_844_, lean_object* v_m_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3(v_00_u03b2_844_, v_m_845_, v_a_846_);
lean_dec_ref(v_a_846_);
lean_dec_ref(v_m_845_);
return v_res_847_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3(lean_object* v_00_u03b2_848_, lean_object* v_a_849_, lean_object* v_x_850_){
_start:
{
uint8_t v___x_851_; 
v___x_851_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_849_, v_x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___boxed(lean_object* v_00_u03b2_852_, lean_object* v_a_853_, lean_object* v_x_854_){
_start:
{
uint8_t v_res_855_; lean_object* v_r_856_; 
v_res_855_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3(v_00_u03b2_852_, v_a_853_, v_x_854_);
lean_dec(v_x_854_);
lean_dec_ref(v_a_853_);
v_r_856_ = lean_box(v_res_855_);
return v_r_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4(lean_object* v_00_u03b2_857_, lean_object* v_data_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(v_data_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5(lean_object* v_00_u03b2_860_, lean_object* v_a_861_, lean_object* v_b_862_, lean_object* v_x_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(v_a_861_, v_b_862_, v_x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7(lean_object* v_00_u03b2_865_, lean_object* v_a_866_, lean_object* v_x_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(v_a_866_, v_x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___boxed(lean_object* v_00_u03b2_869_, lean_object* v_a_870_, lean_object* v_x_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7(v_00_u03b2_869_, v_a_870_, v_x_871_);
lean_dec(v_x_871_);
lean_dec_ref(v_a_870_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_873_, lean_object* v_i_874_, lean_object* v_source_875_, lean_object* v_target_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6___redArg(v_i_874_, v_source_875_, v_target_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_878_, lean_object* v_x_879_, lean_object* v_x_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9___redArg(v_x_879_, v_x_880_);
return v___x_881_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_882_ = lean_box(0);
v___x_883_ = lean_unsigned_to_nat(16u);
v___x_884_ = lean_mk_array(v___x_883_, v___x_882_);
return v___x_884_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_885_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0);
v___x_886_ = lean_unsigned_to_nat(0u);
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v___x_885_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(lean_object* v_e_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_894_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1);
v___x_895_ = lean_st_mk_ref(v___x_894_);
v___x_896_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_e_888_, v___x_895_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_905_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_905_ == 0)
{
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_901_ = lean_st_ref_get(v___x_895_);
lean_dec(v___x_895_);
lean_dec(v___x_901_);
if (v_isShared_900_ == 0)
{
v___x_903_ = v___x_899_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_897_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
else
{
lean_dec(v___x_895_);
return v___x_896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___boxed(lean_object* v_e_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(v_e_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
return v_res_912_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(lean_object* v_m_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_buckets_915_; lean_object* v___x_916_; uint64_t v___x_917_; uint64_t v___x_918_; uint64_t v___x_919_; uint64_t v_fold_920_; uint64_t v___x_921_; uint64_t v___x_922_; uint64_t v___x_923_; size_t v___x_924_; size_t v___x_925_; size_t v___x_926_; size_t v___x_927_; size_t v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v_buckets_915_ = lean_ctor_get(v_m_913_, 1);
v___x_916_ = lean_array_get_size(v_buckets_915_);
v___x_917_ = l_Lean_Expr_hash(v_a_914_);
v___x_918_ = 32ULL;
v___x_919_ = lean_uint64_shift_right(v___x_917_, v___x_918_);
v_fold_920_ = lean_uint64_xor(v___x_917_, v___x_919_);
v___x_921_ = 16ULL;
v___x_922_ = lean_uint64_shift_right(v_fold_920_, v___x_921_);
v___x_923_ = lean_uint64_xor(v_fold_920_, v___x_922_);
v___x_924_ = lean_uint64_to_usize(v___x_923_);
v___x_925_ = lean_usize_of_nat(v___x_916_);
v___x_926_ = ((size_t)1ULL);
v___x_927_ = lean_usize_sub(v___x_925_, v___x_926_);
v___x_928_ = lean_usize_land(v___x_924_, v___x_927_);
v___x_929_ = lean_array_uget_borrowed(v_buckets_915_, v___x_928_);
v___x_930_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_914_, v___x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg___boxed(lean_object* v_m_931_, lean_object* v_a_932_){
_start:
{
uint8_t v_res_933_; lean_object* v_r_934_; 
v_res_933_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_m_931_, v_a_932_);
lean_dec_ref(v_a_932_);
lean_dec_ref(v_m_931_);
v_r_934_ = lean_box(v_res_933_);
return v_r_934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(lean_object* v_m_935_, lean_object* v_a_936_, lean_object* v_b_937_){
_start:
{
lean_object* v_size_938_; lean_object* v_buckets_939_; lean_object* v___x_940_; uint64_t v___x_941_; uint64_t v___x_942_; uint64_t v___x_943_; uint64_t v_fold_944_; uint64_t v___x_945_; uint64_t v___x_946_; uint64_t v___x_947_; size_t v___x_948_; size_t v___x_949_; size_t v___x_950_; size_t v___x_951_; size_t v___x_952_; lean_object* v_bkt_953_; uint8_t v___x_954_; 
v_size_938_ = lean_ctor_get(v_m_935_, 0);
v_buckets_939_ = lean_ctor_get(v_m_935_, 1);
v___x_940_ = lean_array_get_size(v_buckets_939_);
v___x_941_ = l_Lean_Expr_hash(v_a_936_);
v___x_942_ = 32ULL;
v___x_943_ = lean_uint64_shift_right(v___x_941_, v___x_942_);
v_fold_944_ = lean_uint64_xor(v___x_941_, v___x_943_);
v___x_945_ = 16ULL;
v___x_946_ = lean_uint64_shift_right(v_fold_944_, v___x_945_);
v___x_947_ = lean_uint64_xor(v_fold_944_, v___x_946_);
v___x_948_ = lean_uint64_to_usize(v___x_947_);
v___x_949_ = lean_usize_of_nat(v___x_940_);
v___x_950_ = ((size_t)1ULL);
v___x_951_ = lean_usize_sub(v___x_949_, v___x_950_);
v___x_952_ = lean_usize_land(v___x_948_, v___x_951_);
v_bkt_953_ = lean_array_uget_borrowed(v_buckets_939_, v___x_952_);
v___x_954_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_936_, v_bkt_953_);
if (v___x_954_ == 0)
{
lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_975_; 
lean_inc_ref(v_buckets_939_);
lean_inc(v_size_938_);
v_isSharedCheck_975_ = !lean_is_exclusive(v_m_935_);
if (v_isSharedCheck_975_ == 0)
{
lean_object* v_unused_976_; lean_object* v_unused_977_; 
v_unused_976_ = lean_ctor_get(v_m_935_, 1);
lean_dec(v_unused_976_);
v_unused_977_ = lean_ctor_get(v_m_935_, 0);
lean_dec(v_unused_977_);
v___x_956_ = v_m_935_;
v_isShared_957_ = v_isSharedCheck_975_;
goto v_resetjp_955_;
}
else
{
lean_dec(v_m_935_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_975_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v_size_x27_959_; lean_object* v___x_960_; lean_object* v_buckets_x27_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_958_ = lean_unsigned_to_nat(1u);
v_size_x27_959_ = lean_nat_add(v_size_938_, v___x_958_);
lean_dec(v_size_938_);
lean_inc(v_bkt_953_);
v___x_960_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_960_, 0, v_a_936_);
lean_ctor_set(v___x_960_, 1, v_b_937_);
lean_ctor_set(v___x_960_, 2, v_bkt_953_);
v_buckets_x27_961_ = lean_array_uset(v_buckets_939_, v___x_952_, v___x_960_);
v___x_962_ = lean_unsigned_to_nat(4u);
v___x_963_ = lean_nat_mul(v_size_x27_959_, v___x_962_);
v___x_964_ = lean_unsigned_to_nat(3u);
v___x_965_ = lean_nat_div(v___x_963_, v___x_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_array_get_size(v_buckets_x27_961_);
v___x_967_ = lean_nat_dec_le(v___x_965_, v___x_966_);
lean_dec(v___x_965_);
if (v___x_967_ == 0)
{
lean_object* v_val_968_; lean_object* v___x_970_; 
v_val_968_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(v_buckets_x27_961_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 1, v_val_968_);
lean_ctor_set(v___x_956_, 0, v_size_x27_959_);
v___x_970_ = v___x_956_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_size_x27_959_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_val_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
else
{
lean_object* v___x_973_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 1, v_buckets_x27_961_);
lean_ctor_set(v___x_956_, 0, v_size_x27_959_);
v___x_973_ = v___x_956_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_size_x27_959_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_buckets_x27_961_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
else
{
lean_dec(v_b_937_);
lean_dec_ref(v_a_936_);
return v_m_935_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(lean_object* v_e_983_, uint8_t v_omitTopForall_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
switch(lean_obj_tag(v_e_983_))
{
case 4:
{
lean_object* v_declName_991_; lean_object* v___x_992_; lean_object* v_seen_993_; lean_object* v_consts_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1021_; 
v_declName_991_ = lean_ctor_get(v_e_983_, 0);
lean_inc(v_declName_991_);
lean_dec_ref_known(v_e_983_, 2);
v___x_992_ = lean_st_ref_take(v_a_985_);
v_seen_993_ = lean_ctor_get(v___x_992_, 0);
v_consts_994_ = lean_ctor_get(v___x_992_, 1);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_996_ = v___x_992_;
v_isShared_997_ = v_isSharedCheck_1021_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_consts_994_);
lean_inc(v_seen_993_);
lean_dec(v___x_992_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1021_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v___x_1000_; 
lean_inc(v_declName_991_);
v___x_998_ = l_Lean_NameSet_insert(v_consts_994_, v_declName_991_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 1, v___x_998_);
v___x_1000_ = v___x_996_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_seen_993_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1020_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_st_ref_put(v_a_985_, v___x_1000_);
v___x_1002_ = l_Lean_Name_eraseMacroScopes(v_declName_991_);
lean_dec(v_declName_991_);
if (lean_obj_tag(v___x_1002_) == 1)
{
lean_object* v_str_1003_; lean_object* v___x_1004_; uint32_t v___x_1005_; uint32_t v___x_1006_; uint8_t v___x_1007_; 
v_str_1003_ = lean_ctor_get(v___x_1002_, 1);
lean_inc_ref(v_str_1003_);
lean_dec_ref_known(v___x_1002_, 2);
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = lean_string_utf8_get(v_str_1003_, v___x_1004_);
v___x_1006_ = 97;
v___x_1007_ = lean_uint32_dec_le(v___x_1006_, v___x_1005_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = lean_string_utf8_set(v_str_1003_, v___x_1004_, v___x_1005_);
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
return v___x_1009_;
}
else
{
uint32_t v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = 122;
v___x_1011_ = lean_uint32_dec_le(v___x_1005_, v___x_1010_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_string_utf8_set(v_str_1003_, v___x_1004_, v___x_1005_);
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
else
{
uint32_t v___x_1014_; uint32_t v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1014_ = 4294967264;
v___x_1015_ = lean_uint32_add(v___x_1005_, v___x_1014_);
v___x_1016_ = lean_string_utf8_set(v_str_1003_, v___x_1004_, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
return v___x_1017_;
}
}
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
lean_dec(v___x_1002_);
v___x_1018_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
return v___x_1019_;
}
}
}
}
case 5:
{
lean_object* v_fn_1022_; lean_object* v_arg_1023_; uint8_t v___x_1024_; lean_object* v___x_1025_; lean_object* v_a_1026_; lean_object* v___x_1027_; lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1036_; 
v_fn_1022_ = lean_ctor_get(v_e_983_, 0);
lean_inc_ref(v_fn_1022_);
v_arg_1023_ = lean_ctor_get(v_e_983_, 1);
lean_inc_ref(v_arg_1023_);
lean_dec_ref_known(v_e_983_, 2);
v___x_1024_ = 0;
v___x_1025_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_fn_1022_, v___x_1024_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref(v___x_1025_);
v___x_1027_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_arg_1023_, v___x_1024_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1036_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1036_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1032_ = lean_string_append(v_a_1026_, v_a_1028_);
lean_dec(v_a_1028_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1032_);
v___x_1034_ = v___x_1030_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
case 7:
{
lean_object* v_binderType_1037_; lean_object* v_body_1038_; uint8_t v___x_1039_; lean_object* v___x_1040_; lean_object* v_a_1041_; 
v_binderType_1037_ = lean_ctor_get(v_e_983_, 1);
lean_inc_ref(v_binderType_1037_);
v_body_1038_ = lean_ctor_get(v_e_983_, 2);
lean_inc_ref(v_body_1038_);
lean_dec_ref_known(v_e_983_, 3);
v___x_1039_ = 0;
v___x_1040_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_binderType_1037_, v___x_1039_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref(v___x_1040_);
if (v_omitTopForall_984_ == 0)
{
goto v___jp_1042_;
}
else
{
lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1056_ = lean_string_dec_eq(v_a_1041_, v___x_1055_);
if (v___x_1056_ == 0)
{
goto v___jp_1042_;
}
else
{
lean_object* v___x_1057_; 
lean_dec(v_a_1041_);
v___x_1057_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_body_1038_, v_omitTopForall_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
return v___x_1057_;
}
}
v___jp_1042_:
{
lean_object* v___x_1043_; lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1054_; 
v___x_1043_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_body_1038_, v___x_1039_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1046_ = v___x_1043_;
v_isShared_1047_ = v_isSharedCheck_1054_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1043_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1054_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1048_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0));
v___x_1049_ = lean_string_append(v___x_1048_, v_a_1041_);
lean_dec(v_a_1041_);
v___x_1050_ = lean_string_append(v___x_1049_, v_a_1044_);
lean_dec(v_a_1044_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1050_);
v___x_1052_ = v___x_1046_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
case 3:
{
lean_object* v_u_1058_; 
v_u_1058_ = lean_ctor_get(v_e_983_, 0);
lean_inc(v_u_1058_);
lean_dec_ref_known(v_e_983_, 1);
switch(lean_obj_tag(v_u_1058_))
{
case 0:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__1));
v___x_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
return v___x_1060_;
}
case 1:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
lean_dec_ref_known(v_u_1058_, 1);
v___x_1061_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__2));
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
return v___x_1062_;
}
default: 
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
lean_dec(v_u_1058_);
v___x_1063_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__3));
v___x_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
return v___x_1064_;
}
}
}
default: 
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_dec_ref(v_e_983_);
v___x_1065_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(lean_object* v_e_1067_, uint8_t v_omitTopForall_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v___x_1075_; lean_object* v_seen_1076_; uint8_t v___x_1077_; 
v___x_1075_ = lean_st_ref_get(v_a_1069_);
v_seen_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc_ref(v_seen_1076_);
lean_dec(v___x_1075_);
v___x_1077_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_seen_1076_, v_e_1067_);
lean_dec_ref(v_seen_1076_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1099_; 
lean_inc_ref(v_e_1067_);
v___x_1078_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(v_e_1067_, v_omitTopForall_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
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
lean_object* v___x_1083_; lean_object* v_seen_1084_; lean_object* v_consts_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1098_; 
v___x_1083_ = lean_st_ref_take(v_a_1069_);
v_seen_1084_ = lean_ctor_get(v___x_1083_, 0);
v_consts_1085_ = lean_ctor_get(v___x_1083_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1087_ = v___x_1083_;
v_isShared_1088_ = v_isSharedCheck_1098_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_consts_1085_);
lean_inc(v_seen_1084_);
lean_dec(v___x_1083_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1098_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1089_ = lean_box(0);
v___x_1090_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(v_seen_1084_, v_e_1067_, v___x_1089_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1090_);
v___x_1092_ = v___x_1087_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_consts_1085_);
v___x_1092_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1093_ = lean_st_ref_put(v_a_1069_, v___x_1092_);
if (v_isShared_1082_ == 0)
{
v___x_1095_ = v___x_1081_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1079_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec_ref(v_e_1067_);
v___x_1100_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
return v___x_1101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___boxed(lean_object* v_e_1102_, lean_object* v_omitTopForall_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
uint8_t v_omitTopForall_boxed_1110_; lean_object* v_res_1111_; 
v_omitTopForall_boxed_1110_ = lean_unbox(v_omitTopForall_1103_);
v_res_1111_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_e_1102_, v_omitTopForall_boxed_1110_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___boxed(lean_object* v_e_1112_, lean_object* v_omitTopForall_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_){
_start:
{
uint8_t v_omitTopForall_boxed_1120_; lean_object* v_res_1121_; 
v_omitTopForall_boxed_1120_ = lean_unbox(v_omitTopForall_1113_);
v_res_1121_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(v_e_1112_, v_omitTopForall_boxed_1120_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
return v_res_1121_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0(lean_object* v_00_u03b2_1122_, lean_object* v_m_1123_, lean_object* v_a_1124_){
_start:
{
uint8_t v___x_1125_; 
v___x_1125_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_m_1123_, v_a_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___boxed(lean_object* v_00_u03b2_1126_, lean_object* v_m_1127_, lean_object* v_a_1128_){
_start:
{
uint8_t v_res_1129_; lean_object* v_r_1130_; 
v_res_1129_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0(v_00_u03b2_1126_, v_m_1127_, v_a_1128_);
lean_dec_ref(v_a_1128_);
lean_dec_ref(v_m_1127_);
v_r_1130_ = lean_box(v_res_1129_);
return v_r_1130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1(lean_object* v_00_u03b2_1131_, lean_object* v_m_1132_, lean_object* v_a_1133_, lean_object* v_b_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(v_m_1132_, v_a_1133_, v_b_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__3_splitter___redArg(lean_object* v_e_1136_, lean_object* v_h__1_1137_, lean_object* v_h__2_1138_, lean_object* v_h__3_1139_, lean_object* v_h__4_1140_, lean_object* v_h__5_1141_, lean_object* v_h__6_1142_, lean_object* v_h__7_1143_){
_start:
{
switch(lean_obj_tag(v_e_1136_))
{
case 4:
{
lean_object* v_declName_1144_; lean_object* v_us_1145_; lean_object* v___x_1146_; 
lean_dec(v_h__7_1143_);
lean_dec(v_h__6_1142_);
lean_dec(v_h__5_1141_);
lean_dec(v_h__4_1140_);
lean_dec(v_h__3_1139_);
lean_dec(v_h__2_1138_);
v_declName_1144_ = lean_ctor_get(v_e_1136_, 0);
lean_inc(v_declName_1144_);
v_us_1145_ = lean_ctor_get(v_e_1136_, 1);
lean_inc(v_us_1145_);
lean_dec_ref_known(v_e_1136_, 2);
v___x_1146_ = lean_apply_2(v_h__1_1137_, v_declName_1144_, v_us_1145_);
return v___x_1146_;
}
case 5:
{
lean_object* v_fn_1147_; lean_object* v_arg_1148_; lean_object* v___x_1149_; 
lean_dec(v_h__7_1143_);
lean_dec(v_h__6_1142_);
lean_dec(v_h__5_1141_);
lean_dec(v_h__4_1140_);
lean_dec(v_h__3_1139_);
lean_dec(v_h__1_1137_);
v_fn_1147_ = lean_ctor_get(v_e_1136_, 0);
lean_inc_ref(v_fn_1147_);
v_arg_1148_ = lean_ctor_get(v_e_1136_, 1);
lean_inc_ref(v_arg_1148_);
lean_dec_ref_known(v_e_1136_, 2);
v___x_1149_ = lean_apply_2(v_h__2_1138_, v_fn_1147_, v_arg_1148_);
return v___x_1149_;
}
case 7:
{
lean_object* v_binderName_1150_; lean_object* v_binderType_1151_; lean_object* v_body_1152_; uint8_t v_binderInfo_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec(v_h__7_1143_);
lean_dec(v_h__6_1142_);
lean_dec(v_h__5_1141_);
lean_dec(v_h__4_1140_);
lean_dec(v_h__2_1138_);
lean_dec(v_h__1_1137_);
v_binderName_1150_ = lean_ctor_get(v_e_1136_, 0);
lean_inc(v_binderName_1150_);
v_binderType_1151_ = lean_ctor_get(v_e_1136_, 1);
lean_inc_ref(v_binderType_1151_);
v_body_1152_ = lean_ctor_get(v_e_1136_, 2);
lean_inc_ref(v_body_1152_);
v_binderInfo_1153_ = lean_ctor_get_uint8(v_e_1136_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1136_, 3);
v___x_1154_ = lean_box(v_binderInfo_1153_);
v___x_1155_ = lean_apply_4(v_h__3_1139_, v_binderName_1150_, v_binderType_1151_, v_body_1152_, v___x_1154_);
return v___x_1155_;
}
case 3:
{
lean_object* v_u_1156_; 
lean_dec(v_h__7_1143_);
lean_dec(v_h__3_1139_);
lean_dec(v_h__2_1138_);
lean_dec(v_h__1_1137_);
v_u_1156_ = lean_ctor_get(v_e_1136_, 0);
lean_inc(v_u_1156_);
lean_dec_ref_known(v_e_1136_, 1);
switch(lean_obj_tag(v_u_1156_))
{
case 0:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_dec(v_h__6_1142_);
lean_dec(v_h__5_1141_);
v___x_1157_ = lean_box(0);
v___x_1158_ = lean_apply_1(v_h__4_1140_, v___x_1157_);
return v___x_1158_;
}
case 1:
{
lean_object* v_a_1159_; lean_object* v___x_1160_; 
lean_dec(v_h__6_1142_);
lean_dec(v_h__4_1140_);
v_a_1159_ = lean_ctor_get(v_u_1156_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v_u_1156_, 1);
v___x_1160_ = lean_apply_1(v_h__5_1141_, v_a_1159_);
return v___x_1160_;
}
default: 
{
lean_object* v___x_1161_; 
lean_dec(v_h__5_1141_);
lean_dec(v_h__4_1140_);
v___x_1161_ = lean_apply_3(v_h__6_1142_, v_u_1156_, lean_box(0), lean_box(0));
return v___x_1161_;
}
}
}
default: 
{
lean_object* v___x_1162_; 
lean_dec(v_h__6_1142_);
lean_dec(v_h__5_1141_);
lean_dec(v_h__4_1140_);
lean_dec(v_h__3_1139_);
lean_dec(v_h__2_1138_);
lean_dec(v_h__1_1137_);
v___x_1162_ = lean_apply_7(v_h__7_1143_, v_e_1136_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1162_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__3_splitter(lean_object* v_motive_1163_, lean_object* v_e_1164_, lean_object* v_h__1_1165_, lean_object* v_h__2_1166_, lean_object* v_h__3_1167_, lean_object* v_h__4_1168_, lean_object* v_h__5_1169_, lean_object* v_h__6_1170_, lean_object* v_h__7_1171_){
_start:
{
switch(lean_obj_tag(v_e_1164_))
{
case 4:
{
lean_object* v_declName_1172_; lean_object* v_us_1173_; lean_object* v___x_1174_; 
lean_dec(v_h__7_1171_);
lean_dec(v_h__6_1170_);
lean_dec(v_h__5_1169_);
lean_dec(v_h__4_1168_);
lean_dec(v_h__3_1167_);
lean_dec(v_h__2_1166_);
v_declName_1172_ = lean_ctor_get(v_e_1164_, 0);
lean_inc(v_declName_1172_);
v_us_1173_ = lean_ctor_get(v_e_1164_, 1);
lean_inc(v_us_1173_);
lean_dec_ref_known(v_e_1164_, 2);
v___x_1174_ = lean_apply_2(v_h__1_1165_, v_declName_1172_, v_us_1173_);
return v___x_1174_;
}
case 5:
{
lean_object* v_fn_1175_; lean_object* v_arg_1176_; lean_object* v___x_1177_; 
lean_dec(v_h__7_1171_);
lean_dec(v_h__6_1170_);
lean_dec(v_h__5_1169_);
lean_dec(v_h__4_1168_);
lean_dec(v_h__3_1167_);
lean_dec(v_h__1_1165_);
v_fn_1175_ = lean_ctor_get(v_e_1164_, 0);
lean_inc_ref(v_fn_1175_);
v_arg_1176_ = lean_ctor_get(v_e_1164_, 1);
lean_inc_ref(v_arg_1176_);
lean_dec_ref_known(v_e_1164_, 2);
v___x_1177_ = lean_apply_2(v_h__2_1166_, v_fn_1175_, v_arg_1176_);
return v___x_1177_;
}
case 7:
{
lean_object* v_binderName_1178_; lean_object* v_binderType_1179_; lean_object* v_body_1180_; uint8_t v_binderInfo_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_dec(v_h__7_1171_);
lean_dec(v_h__6_1170_);
lean_dec(v_h__5_1169_);
lean_dec(v_h__4_1168_);
lean_dec(v_h__2_1166_);
lean_dec(v_h__1_1165_);
v_binderName_1178_ = lean_ctor_get(v_e_1164_, 0);
lean_inc(v_binderName_1178_);
v_binderType_1179_ = lean_ctor_get(v_e_1164_, 1);
lean_inc_ref(v_binderType_1179_);
v_body_1180_ = lean_ctor_get(v_e_1164_, 2);
lean_inc_ref(v_body_1180_);
v_binderInfo_1181_ = lean_ctor_get_uint8(v_e_1164_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1164_, 3);
v___x_1182_ = lean_box(v_binderInfo_1181_);
v___x_1183_ = lean_apply_4(v_h__3_1167_, v_binderName_1178_, v_binderType_1179_, v_body_1180_, v___x_1182_);
return v___x_1183_;
}
case 3:
{
lean_object* v_u_1184_; 
lean_dec(v_h__7_1171_);
lean_dec(v_h__3_1167_);
lean_dec(v_h__2_1166_);
lean_dec(v_h__1_1165_);
v_u_1184_ = lean_ctor_get(v_e_1164_, 0);
lean_inc(v_u_1184_);
lean_dec_ref_known(v_e_1164_, 1);
switch(lean_obj_tag(v_u_1184_))
{
case 0:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_dec(v_h__6_1170_);
lean_dec(v_h__5_1169_);
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_apply_1(v_h__4_1168_, v___x_1185_);
return v___x_1186_;
}
case 1:
{
lean_object* v_a_1187_; lean_object* v___x_1188_; 
lean_dec(v_h__6_1170_);
lean_dec(v_h__4_1168_);
v_a_1187_ = lean_ctor_get(v_u_1184_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v_u_1184_, 1);
v___x_1188_ = lean_apply_1(v_h__5_1169_, v_a_1187_);
return v___x_1188_;
}
default: 
{
lean_object* v___x_1189_; 
lean_dec(v_h__5_1169_);
lean_dec(v_h__4_1168_);
v___x_1189_ = lean_apply_3(v_h__6_1170_, v_u_1184_, lean_box(0), lean_box(0));
return v___x_1189_;
}
}
}
default: 
{
lean_object* v___x_1190_; 
lean_dec(v_h__6_1170_);
lean_dec(v_h__5_1169_);
lean_dec(v_h__4_1168_);
lean_dec(v_h__3_1167_);
lean_dec(v_h__2_1166_);
lean_dec(v_h__1_1165_);
v___x_1190_ = lean_apply_7(v_h__7_1171_, v_e_1164_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1190_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__1_splitter___redArg(lean_object* v_x_1191_, lean_object* v_h__1_1192_, lean_object* v_h__2_1193_){
_start:
{
if (lean_obj_tag(v_x_1191_) == 1)
{
lean_object* v_pre_1194_; lean_object* v_str_1195_; lean_object* v___x_1196_; 
lean_dec(v_h__2_1193_);
v_pre_1194_ = lean_ctor_get(v_x_1191_, 0);
lean_inc(v_pre_1194_);
v_str_1195_ = lean_ctor_get(v_x_1191_, 1);
lean_inc_ref(v_str_1195_);
lean_dec_ref_known(v_x_1191_, 2);
v___x_1196_ = lean_apply_2(v_h__1_1192_, v_pre_1194_, v_str_1195_);
return v___x_1196_;
}
else
{
lean_object* v___x_1197_; 
lean_dec(v_h__1_1192_);
v___x_1197_ = lean_apply_2(v_h__2_1193_, v_x_1191_, lean_box(0));
return v___x_1197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__1_splitter(lean_object* v_motive_1198_, lean_object* v_x_1199_, lean_object* v_h__1_1200_, lean_object* v_h__2_1201_){
_start:
{
if (lean_obj_tag(v_x_1199_) == 1)
{
lean_object* v_pre_1202_; lean_object* v_str_1203_; lean_object* v___x_1204_; 
lean_dec(v_h__2_1201_);
v_pre_1202_ = lean_ctor_get(v_x_1199_, 0);
lean_inc(v_pre_1202_);
v_str_1203_ = lean_ctor_get(v_x_1199_, 1);
lean_inc_ref(v_str_1203_);
lean_dec_ref_known(v_x_1199_, 2);
v___x_1204_ = lean_apply_2(v_h__1_1200_, v_pre_1202_, v_str_1203_);
return v___x_1204_;
}
else
{
lean_object* v___x_1205_; 
lean_dec(v_h__1_1200_);
v___x_1205_ = lean_apply_2(v_h__2_1201_, v_x_1199_, lean_box(0));
return v___x_1205_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore(lean_object* v_e_1206_, uint8_t v_omitTopForall_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_e_1206_, v_omitTopForall_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore___boxed(lean_object* v_e_1215_, lean_object* v_omitTopForall_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
uint8_t v_omitTopForall_boxed_1223_; lean_object* v_res_1224_; 
v_omitTopForall_boxed_1223_ = lean_unbox(v_omitTopForall_1216_);
v_res_1224_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore(v_e_1215_, v_omitTopForall_boxed_1223_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(lean_object* v_e_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
if (lean_obj_tag(v_e_1226_) == 7)
{
lean_object* v_binderType_1233_; lean_object* v_body_1234_; lean_object* v___x_1235_; 
v_binderType_1233_ = lean_ctor_get(v_e_1226_, 1);
lean_inc_ref(v_binderType_1233_);
v_body_1234_ = lean_ctor_get(v_e_1226_, 2);
lean_inc_ref(v_body_1234_);
lean_dec_ref_known(v_e_1226_, 3);
v___x_1235_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(v_body_1234_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v_fst_1237_; lean_object* v_snd_1238_; uint8_t v___x_1239_; lean_object* v___x_1240_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1236_);
lean_dec_ref_known(v___x_1235_, 1);
v_fst_1237_ = lean_ctor_get(v_a_1236_, 0);
v_snd_1238_ = lean_ctor_get(v_a_1236_, 1);
v___x_1239_ = 1;
v___x_1240_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_binderType_1233_, v___x_1239_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1265_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1265_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1265_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1245_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1246_ = lean_string_dec_eq(v_a_1241_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1259_; 
lean_inc(v_snd_1238_);
lean_inc(v_fst_1237_);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_a_1236_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; lean_object* v_unused_1261_; 
v_unused_1260_ = lean_ctor_get(v_a_1236_, 1);
lean_dec(v_unused_1260_);
v_unused_1261_ = lean_ctor_get(v_a_1236_, 0);
lean_dec(v_unused_1261_);
v___x_1248_ = v_a_1236_;
v_isShared_1249_ = v_isSharedCheck_1259_;
goto v_resetjp_1247_;
}
else
{
lean_dec(v_a_1236_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1259_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1250_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit___closed__0));
v___x_1251_ = lean_string_append(v___x_1250_, v_a_1241_);
lean_dec(v_a_1241_);
v___x_1252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v_fst_1237_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v___x_1252_);
v___x_1254_ = v___x_1248_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_snd_1238_);
v___x_1254_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1256_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v___x_1254_);
v___x_1256_ = v___x_1243_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
else
{
lean_object* v___x_1263_; 
lean_dec(v_a_1241_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v_a_1236_);
v___x_1263_ = v___x_1243_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1236_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_a_1236_);
v_a_1266_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1240_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1240_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
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
else
{
lean_dec_ref(v_binderType_1233_);
return v___x_1235_;
}
}
else
{
uint8_t v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = 0;
v___x_1275_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_e_1226_, v___x_1274_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1285_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1285_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1285_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1280_ = lean_box(0);
v___x_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
lean_ctor_set(v___x_1281_, 1, v_a_1276_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1281_);
v___x_1283_ = v___x_1278_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
v_a_1286_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1275_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1275_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit___boxed(lean_object* v_e_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(v_e_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(lean_object* v_x_1302_, lean_object* v_x_1303_){
_start:
{
if (lean_obj_tag(v_x_1303_) == 0)
{
return v_x_1302_;
}
else
{
lean_object* v_head_1304_; lean_object* v_tail_1305_; lean_object* v___x_1306_; 
v_head_1304_ = lean_ctor_get(v_x_1303_, 0);
v_tail_1305_ = lean_ctor_get(v_x_1303_, 1);
v___x_1306_ = lean_string_append(v_x_1302_, v_head_1304_);
v_x_1302_ = v___x_1306_;
v_x_1303_ = v_tail_1305_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0___boxed(lean_object* v_x_1308_, lean_object* v_x_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(v_x_1308_, v_x_1309_);
lean_dec(v_x_1309_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(lean_object* v_e_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(v_e_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1331_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1321_ = v___x_1318_;
v_isShared_1322_ = v_isSharedCheck_1331_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1331_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v_fst_1323_; lean_object* v_snd_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1329_; 
v_fst_1323_ = lean_ctor_get(v_a_1319_, 0);
lean_inc(v_fst_1323_);
v_snd_1324_ = lean_ctor_get(v_a_1319_, 1);
lean_inc(v_snd_1324_);
lean_dec(v_a_1319_);
v___x_1325_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1326_ = l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(v___x_1325_, v_fst_1323_);
lean_dec(v_fst_1323_);
v___x_1327_ = lean_string_append(v_snd_1324_, v___x_1326_);
lean_dec_ref(v___x_1326_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v___x_1327_);
v___x_1329_ = v___x_1321_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
v_a_1332_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1318_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1318_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux___boxed(lean_object* v_e_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(v_e_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec(v_a_1343_);
lean_dec_ref(v_a_1342_);
lean_dec(v_a_1341_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(lean_object* v_ns_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
switch(lean_obj_tag(v_ns_1348_))
{
case 0:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = lean_box(0);
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
return v___x_1353_;
}
case 1:
{
lean_object* v_pre_1354_; lean_object* v___x_1355_; lean_object* v_env_1356_; uint8_t v___x_1357_; uint8_t v___x_1358_; 
v_pre_1354_ = lean_ctor_get(v_ns_1348_, 0);
lean_inc(v_pre_1354_);
v___x_1355_ = lean_st_ref_get(v_a_1350_);
v_env_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc_ref(v_env_1356_);
lean_dec(v___x_1355_);
v___x_1357_ = 1;
lean_inc_ref(v_ns_1348_);
v___x_1358_ = l_Lean_Environment_contains(v_env_1356_, v_ns_1348_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_dec_ref_known(v_ns_1348_, 2);
v_ns_1348_ = v_pre_1354_;
goto _start;
}
else
{
lean_object* v___x_1360_; lean_object* v_seen_1361_; lean_object* v_consts_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1376_; 
v___x_1360_ = lean_st_ref_take(v_a_1349_);
v_seen_1361_ = lean_ctor_get(v___x_1360_, 0);
v_consts_1362_ = lean_ctor_get(v___x_1360_, 1);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1364_ = v___x_1360_;
v_isShared_1365_ = v_isSharedCheck_1376_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_consts_1362_);
lean_inc(v_seen_1361_);
lean_dec(v___x_1360_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1376_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1366_ = lean_box(0);
lean_inc_ref(v_ns_1348_);
v___x_1367_ = l_Lean_Expr_const___override(v_ns_1348_, v___x_1366_);
v___x_1368_ = lean_box(0);
v___x_1369_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(v_seen_1361_, v___x_1367_, v___x_1368_);
v___x_1370_ = l_Lean_NameSet_insert(v_consts_1362_, v_ns_1348_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v___x_1370_);
lean_ctor_set(v___x_1364_, 0, v___x_1369_);
v___x_1372_ = v___x_1364_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v___x_1373_; 
v___x_1373_ = lean_st_ref_put(v_a_1349_, v___x_1372_);
v_ns_1348_ = v_pre_1354_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_pre_1377_; 
v_pre_1377_ = lean_ctor_get(v_ns_1348_, 0);
lean_inc(v_pre_1377_);
lean_dec_ref_known(v_ns_1348_, 2);
v_ns_1348_ = v_pre_1377_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg___boxed(lean_object* v_ns_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(v_ns_1379_, v_a_1380_, v_a_1381_);
lean_dec(v_a_1381_);
lean_dec(v_a_1380_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace(lean_object* v_ns_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(v_ns_1384_, v_a_1385_, v_a_1389_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___boxed(lean_object* v_ns_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace(v_ns_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(lean_object* v_e_1400_, lean_object* v___y_1401_){
_start:
{
uint8_t v___x_1403_; 
v___x_1403_ = l_Lean_Expr_hasMVar(v_e_1400_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; 
v___x_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1404_, 0, v_e_1400_);
return v___x_1404_;
}
else
{
lean_object* v___x_1405_; lean_object* v_mctx_1406_; lean_object* v___x_1407_; lean_object* v_fst_1408_; lean_object* v_snd_1409_; lean_object* v___x_1410_; lean_object* v_cache_1411_; lean_object* v_zetaDeltaFVarIds_1412_; lean_object* v_postponed_1413_; lean_object* v_diag_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1423_; 
v___x_1405_ = lean_st_ref_get(v___y_1401_);
v_mctx_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc_ref(v_mctx_1406_);
lean_dec(v___x_1405_);
v___x_1407_ = l_Lean_instantiateMVarsCore(v_mctx_1406_, v_e_1400_);
v_fst_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_fst_1408_);
v_snd_1409_ = lean_ctor_get(v___x_1407_, 1);
lean_inc(v_snd_1409_);
lean_dec_ref(v___x_1407_);
v___x_1410_ = lean_st_ref_take(v___y_1401_);
v_cache_1411_ = lean_ctor_get(v___x_1410_, 1);
v_zetaDeltaFVarIds_1412_ = lean_ctor_get(v___x_1410_, 2);
v_postponed_1413_ = lean_ctor_get(v___x_1410_, 3);
v_diag_1414_ = lean_ctor_get(v___x_1410_, 4);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v___x_1410_, 0);
lean_dec(v_unused_1424_);
v___x_1416_ = v___x_1410_;
v_isShared_1417_ = v_isSharedCheck_1423_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_diag_1414_);
lean_inc(v_postponed_1413_);
lean_inc(v_zetaDeltaFVarIds_1412_);
lean_inc(v_cache_1411_);
lean_dec(v___x_1410_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1423_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v_snd_1409_);
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_snd_1409_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_cache_1411_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v_zetaDeltaFVarIds_1412_);
lean_ctor_set(v_reuseFailAlloc_1422_, 3, v_postponed_1413_);
lean_ctor_set(v_reuseFailAlloc_1422_, 4, v_diag_1414_);
v___x_1419_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = lean_st_ref_put(v___y_1401_, v___x_1419_);
v___x_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1421_, 0, v_fst_1408_);
return v___x_1421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg___boxed(lean_object* v_e_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_1425_, v___y_1426_);
lean_dec(v___y_1426_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0(lean_object* v_e_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_1429_, v___y_1432_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___boxed(lean_object* v_e_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0(v_e_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(lean_object* v_e_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v___x_1452_; lean_object* v_toCold_1453_; lean_object* v_a_1454_; lean_object* v_currNamespace_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1452_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_1445_, v_a_1448_);
v_toCold_1453_ = lean_ctor_get(v_a_1449_, 0);
v_a_1454_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_a_1454_);
lean_dec_ref(v___x_1452_);
v_currNamespace_1455_ = lean_ctor_get(v_toCold_1453_, 4);
lean_inc(v_currNamespace_1455_);
v___x_1456_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(v_currNamespace_1455_, v_a_1446_, v_a_1450_);
lean_dec_ref(v___x_1456_);
v___x_1457_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(v_a_1454_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1459_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v___x_1459_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(v_a_1458_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
return v___x_1459_;
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
v_a_1460_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1457_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1457_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName___boxed(lean_object* v_e_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(v_e_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec(v_a_1469_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(lean_object* v_x_1477_){
_start:
{
switch(lean_obj_tag(v_x_1477_))
{
case 0:
{
lean_object* v___x_1478_; 
v___x_1478_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
return v___x_1478_;
}
case 1:
{
lean_object* v_pre_1479_; lean_object* v_str_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; uint32_t v___x_1485_; uint32_t v___x_1486_; uint8_t v___x_1487_; 
v_pre_1479_ = lean_ctor_get(v_x_1477_, 0);
lean_inc(v_pre_1479_);
v_str_1480_ = lean_ctor_get(v_x_1477_, 1);
lean_inc_ref(v_str_1480_);
lean_dec_ref_known(v_x_1477_, 2);
v___x_1481_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(v_pre_1479_);
v___x_1482_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix___closed__0));
v___x_1483_ = lean_string_append(v___x_1481_, v___x_1482_);
v___x_1484_ = lean_unsigned_to_nat(0u);
v___x_1485_ = lean_string_utf8_get(v_str_1480_, v___x_1484_);
v___x_1486_ = 65;
v___x_1487_ = lean_uint32_dec_le(v___x_1486_, v___x_1485_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_string_utf8_set(v_str_1480_, v___x_1484_, v___x_1485_);
v___x_1489_ = lean_string_append(v___x_1483_, v___x_1488_);
lean_dec_ref(v___x_1488_);
return v___x_1489_;
}
else
{
uint32_t v___x_1490_; uint8_t v___x_1491_; 
v___x_1490_ = 90;
v___x_1491_ = lean_uint32_dec_le(v___x_1485_, v___x_1490_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = lean_string_utf8_set(v_str_1480_, v___x_1484_, v___x_1485_);
v___x_1493_ = lean_string_append(v___x_1483_, v___x_1492_);
lean_dec_ref(v___x_1492_);
return v___x_1493_;
}
else
{
uint32_t v___x_1494_; uint32_t v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1494_ = 32;
v___x_1495_ = lean_uint32_add(v___x_1485_, v___x_1494_);
v___x_1496_ = lean_string_utf8_set(v_str_1480_, v___x_1484_, v___x_1495_);
v___x_1497_ = lean_string_append(v___x_1483_, v___x_1496_);
lean_dec_ref(v___x_1496_);
return v___x_1497_;
}
}
}
default: 
{
lean_object* v_pre_1498_; 
v_pre_1498_ = lean_ctor_get(v_x_1477_, 0);
lean_inc(v_pre_1498_);
lean_dec_ref_known(v_x_1477_, 2);
v_x_1477_ = v_pre_1498_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(lean_object* v___y_1500_){
_start:
{
lean_object* v___x_1502_; lean_object* v_env_1503_; lean_object* v___x_1504_; lean_object* v_mainModule_1505_; lean_object* v___x_1506_; 
v___x_1502_ = lean_st_ref_get(v___y_1500_);
v_env_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc_ref(v_env_1503_);
lean_dec(v___x_1502_);
v___x_1504_ = l_Lean_Environment_header(v_env_1503_);
lean_dec_ref(v_env_1503_);
v_mainModule_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_mainModule_1505_);
lean_dec_ref(v___x_1504_);
v___x_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1506_, 0, v_mainModule_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg___boxed(lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v___y_1507_);
lean_dec(v___y_1507_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1(lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v___y_1513_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___boxed(lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1(v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
return v_res_1521_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(lean_object* v_x_1522_, lean_object* v_x_1523_){
_start:
{
if (lean_obj_tag(v_x_1522_) == 0)
{
if (lean_obj_tag(v_x_1523_) == 0)
{
uint8_t v___x_1524_; 
v___x_1524_ = 1;
return v___x_1524_;
}
else
{
uint8_t v___x_1525_; 
v___x_1525_ = 0;
return v___x_1525_;
}
}
else
{
if (lean_obj_tag(v_x_1523_) == 0)
{
uint8_t v___x_1526_; 
v___x_1526_ = 0;
return v___x_1526_;
}
else
{
lean_object* v_val_1527_; lean_object* v_val_1528_; uint8_t v___x_1529_; 
v_val_1527_ = lean_ctor_get(v_x_1522_, 0);
v_val_1528_ = lean_ctor_get(v_x_1523_, 0);
v___x_1529_ = lean_name_eq(v_val_1527_, v_val_1528_);
return v___x_1529_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2___boxed(lean_object* v_x_1530_, lean_object* v_x_1531_){
_start:
{
uint8_t v_res_1532_; lean_object* v_r_1533_; 
v_res_1532_ = l_instBEqOption_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(v_x_1530_, v_x_1531_);
lean_dec(v_x_1531_);
lean_dec(v_x_1530_);
v_r_1533_ = lean_box(v_res_1532_);
return v_r_1533_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0(lean_object* v_e_1534_){
_start:
{
if (lean_obj_tag(v_e_1534_) == 4)
{
lean_object* v_declName_1535_; uint8_t v___x_1536_; 
v_declName_1535_ = lean_ctor_get(v_e_1534_, 0);
v___x_1536_ = l_Lean_Name_hasMacroScopes(v_declName_1535_);
return v___x_1536_;
}
else
{
uint8_t v___x_1537_; 
v___x_1537_ = 0;
return v___x_1537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0___boxed(lean_object* v_e_1538_){
_start:
{
uint8_t v_res_1539_; lean_object* v_r_1540_; 
v_res_1539_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0(v_e_1538_);
lean_dec_ref(v_e_1538_);
v_r_1540_ = lean_box(v_res_1539_);
return v_r_1540_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(lean_object* v_as_1541_, size_t v_i_1542_, size_t v_stop_1543_){
_start:
{
uint8_t v___x_1544_; 
v___x_1544_ = lean_usize_dec_eq(v_i_1542_, v_stop_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; 
v___x_1545_ = lean_array_uget_borrowed(v_as_1541_, v_i_1542_);
if (lean_obj_tag(v___x_1545_) == 0)
{
uint8_t v___x_1546_; 
v___x_1546_ = 1;
return v___x_1546_;
}
else
{
size_t v___x_1547_; size_t v___x_1548_; 
v___x_1547_ = ((size_t)1ULL);
v___x_1548_ = lean_usize_add(v_i_1542_, v___x_1547_);
v_i_1542_ = v___x_1548_;
goto _start;
}
}
else
{
uint8_t v___x_1550_; 
v___x_1550_ = 0;
return v___x_1550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5___boxed(lean_object* v_as_1551_, lean_object* v_i_1552_, lean_object* v_stop_1553_){
_start:
{
size_t v_i_boxed_1554_; size_t v_stop_boxed_1555_; uint8_t v_res_1556_; lean_object* v_r_1557_; 
v_i_boxed_1554_ = lean_unbox_usize(v_i_1552_);
lean_dec(v_i_1552_);
v_stop_boxed_1555_ = lean_unbox_usize(v_stop_1553_);
lean_dec(v_stop_1553_);
v_res_1556_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(v_as_1551_, v_i_boxed_1554_, v_stop_boxed_1555_);
lean_dec_ref(v_as_1551_);
v_r_1557_ = lean_box(v_res_1556_);
return v_r_1557_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(lean_object* v___x_1558_, lean_object* v_as_1559_, size_t v_i_1560_, size_t v_stop_1561_){
_start:
{
uint8_t v___x_1562_; 
v___x_1562_ = lean_usize_dec_eq(v_i_1560_, v_stop_1561_);
if (v___x_1562_ == 0)
{
uint8_t v___x_1563_; lean_object* v___y_1565_; lean_object* v___x_1571_; 
v___x_1563_ = 1;
v___x_1571_ = lean_array_uget(v_as_1559_, v_i_1560_);
if (lean_obj_tag(v___x_1571_) == 0)
{
v___y_1565_ = v___x_1571_;
goto v___jp_1564_;
}
else
{
lean_object* v_val_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1580_; 
v_val_1572_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1574_ = v___x_1571_;
v_isShared_1575_ = v_isSharedCheck_1580_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_val_1572_);
lean_dec(v___x_1571_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1580_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1576_ = l_Lean_Name_getRoot(v_val_1572_);
lean_dec(v_val_1572_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v___x_1576_);
v___x_1578_ = v___x_1574_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
v___y_1565_ = v___x_1578_;
goto v___jp_1564_;
}
}
}
v___jp_1564_:
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
lean_inc(v___x_1558_);
v___x_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1558_);
v___x_1567_ = l_instBEqOption_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(v___y_1565_, v___x_1566_);
lean_dec_ref_known(v___x_1566_, 1);
lean_dec(v___y_1565_);
if (v___x_1567_ == 0)
{
size_t v___x_1568_; size_t v___x_1569_; 
v___x_1568_ = ((size_t)1ULL);
v___x_1569_ = lean_usize_add(v_i_1560_, v___x_1568_);
v_i_1560_ = v___x_1569_;
goto _start;
}
else
{
lean_dec(v___x_1558_);
return v___x_1563_;
}
}
}
else
{
uint8_t v___x_1581_; 
lean_dec(v___x_1558_);
v___x_1581_ = 0;
return v___x_1581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4___boxed(lean_object* v___x_1582_, lean_object* v_as_1583_, lean_object* v_i_1584_, lean_object* v_stop_1585_){
_start:
{
size_t v_i_boxed_1586_; size_t v_stop_boxed_1587_; uint8_t v_res_1588_; lean_object* v_r_1589_; 
v_i_boxed_1586_ = lean_unbox_usize(v_i_1584_);
lean_dec(v_i_1584_);
v_stop_boxed_1587_ = lean_unbox_usize(v_stop_1585_);
lean_dec(v_stop_1585_);
v_res_1588_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(v___x_1582_, v_as_1583_, v_i_boxed_1586_, v_stop_boxed_1587_);
lean_dec_ref(v_as_1583_);
v_r_1589_ = lean_box(v_res_1588_);
return v_r_1589_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1590_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
return v___x_1592_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1593_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1594_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_1595_ = lean_unsigned_to_nat(0u);
v___x_1596_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
lean_ctor_set(v___x_1596_, 2, v___x_1595_);
lean_ctor_set(v___x_1596_, 3, v___x_1595_);
lean_ctor_set(v___x_1596_, 4, v___x_1594_);
lean_ctor_set(v___x_1596_, 5, v___x_1594_);
lean_ctor_set(v___x_1596_, 6, v___x_1594_);
lean_ctor_set(v___x_1596_, 7, v___x_1594_);
lean_ctor_set(v___x_1596_, 8, v___x_1594_);
lean_ctor_set(v___x_1596_, 9, v___x_1594_);
lean_ctor_set(v___x_1596_, 10, v___x_1594_);
lean_ctor_set(v___x_1596_, 11, v___x_1593_);
return v___x_1596_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = lean_unsigned_to_nat(32u);
v___x_1598_ = lean_mk_empty_array_with_capacity(v___x_1597_);
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
return v___x_1599_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1600_ = ((size_t)5ULL);
v___x_1601_ = lean_unsigned_to_nat(0u);
v___x_1602_ = lean_unsigned_to_nat(32u);
v___x_1603_ = lean_mk_empty_array_with_capacity(v___x_1602_);
v___x_1604_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_1605_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
lean_ctor_set(v___x_1605_, 1, v___x_1603_);
lean_ctor_set(v___x_1605_, 2, v___x_1601_);
lean_ctor_set(v___x_1605_, 3, v___x_1601_);
lean_ctor_set_usize(v___x_1605_, 4, v___x_1600_);
return v___x_1605_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1606_ = lean_box(1);
v___x_1607_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_1608_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_1609_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
lean_ctor_set(v___x_1609_, 1, v___x_1607_);
lean_ctor_set(v___x_1609_, 2, v___x_1606_);
return v___x_1609_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_1612_ = l_Lean_stringToMessageData(v___x_1611_);
return v___x_1612_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_1615_ = l_Lean_stringToMessageData(v___x_1614_);
return v___x_1615_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_1618_ = l_Lean_stringToMessageData(v___x_1617_);
return v___x_1618_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_1621_ = l_Lean_stringToMessageData(v___x_1620_);
return v___x_1621_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__14));
v___x_1624_ = l_Lean_stringToMessageData(v___x_1623_);
return v___x_1624_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__16));
v___x_1627_ = l_Lean_stringToMessageData(v___x_1626_);
return v___x_1627_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__18));
v___x_1630_ = l_Lean_stringToMessageData(v___x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_1631_, lean_object* v_declHint_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v_env_1637_; uint8_t v___x_1638_; 
v___x_1635_ = lean_box(0);
v___x_1636_ = lean_st_ref_get(v___y_1633_);
v_env_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc_ref(v_env_1637_);
lean_dec(v___x_1636_);
v___x_1638_ = l_Lean_Name_isAnonymous(v_declHint_1632_);
if (v___x_1638_ == 0)
{
uint8_t v_isExporting_1639_; 
v_isExporting_1639_ = lean_ctor_get_uint8(v_env_1637_, sizeof(void*)*13);
if (v_isExporting_1639_ == 0)
{
lean_object* v___x_1640_; 
lean_dec_ref(v_env_1637_);
lean_dec(v_declHint_1632_);
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v_msg_1631_);
return v___x_1640_;
}
else
{
lean_object* v___x_1641_; uint8_t v___x_1642_; 
lean_inc_ref(v_env_1637_);
v___x_1641_ = l_Lean_Environment_setExporting(v_env_1637_, v___x_1638_);
lean_inc(v_declHint_1632_);
lean_inc_ref(v___x_1641_);
v___x_1642_ = l_Lean_Environment_contains(v___x_1641_, v_declHint_1632_, v_isExporting_1639_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; 
lean_dec_ref(v___x_1641_);
lean_dec_ref(v_env_1637_);
lean_dec(v_declHint_1632_);
v___x_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1643_, 0, v_msg_1631_);
return v___x_1643_;
}
else
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v_c_1649_; lean_object* v___x_1650_; 
v___x_1644_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_1645_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5);
v___x_1646_ = l_Lean_Options_empty;
v___x_1647_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1641_);
lean_ctor_set(v___x_1647_, 1, v___x_1644_);
lean_ctor_set(v___x_1647_, 2, v___x_1645_);
lean_ctor_set(v___x_1647_, 3, v___x_1646_);
lean_inc(v_declHint_1632_);
v___x_1648_ = l_Lean_MessageData_ofConstName(v_declHint_1632_, v___x_1638_);
v_c_1649_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1649_, 0, v___x_1647_);
lean_ctor_set(v_c_1649_, 1, v___x_1648_);
v___x_1650_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1637_, v_declHint_1632_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_dec_ref(v_env_1637_);
lean_dec(v_declHint_1632_);
v___x_1651_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
lean_ctor_set(v___x_1652_, 1, v_c_1649_);
v___x_1653_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9);
v___x_1654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1652_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = l_Lean_MessageData_note(v___x_1654_);
v___x_1656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1656_, 0, v_msg_1631_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
return v___x_1657_;
}
else
{
lean_object* v_val_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1692_; 
v_val_1658_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1660_ = v___x_1650_;
v_isShared_1661_ = v_isSharedCheck_1692_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_val_1658_);
lean_dec(v___x_1650_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1692_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v_moduleNames_1663_; lean_object* v_mod_1664_; uint8_t v___x_1665_; 
v___x_1662_ = l_Lean_Environment_header(v_env_1637_);
lean_dec_ref(v_env_1637_);
v_moduleNames_1663_ = lean_ctor_get(v___x_1662_, 4);
lean_inc_ref(v_moduleNames_1663_);
lean_dec_ref(v___x_1662_);
v_mod_1664_ = lean_array_get(v___x_1635_, v_moduleNames_1663_, v_val_1658_);
lean_dec(v_val_1658_);
lean_dec_ref(v_moduleNames_1663_);
v___x_1665_ = l_Lean_isPrivateName(v_declHint_1632_);
lean_dec(v_declHint_1632_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1666_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
lean_ctor_set(v___x_1667_, 1, v_c_1649_);
v___x_1668_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = l_Lean_MessageData_ofName(v_mod_1664_);
v___x_1671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_1673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1671_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = l_Lean_MessageData_note(v___x_1673_);
v___x_1675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1675_, 0, v_msg_1631_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set_tag(v___x_1660_, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1675_);
v___x_1677_ = v___x_1660_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1679_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_1680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
lean_ctor_set(v___x_1680_, 1, v_c_1649_);
v___x_1681_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17);
v___x_1682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1680_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
v___x_1683_ = l_Lean_MessageData_ofName(v_mod_1664_);
v___x_1684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1682_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
v___x_1685_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19);
v___x_1686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1684_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
v___x_1687_ = l_Lean_MessageData_note(v___x_1686_);
v___x_1688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1688_, 0, v_msg_1631_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set_tag(v___x_1660_, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1688_);
v___x_1690_ = v___x_1660_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1693_; 
lean_dec_ref(v_env_1637_);
lean_dec(v_declHint_1632_);
v___x_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1693_, 0, v_msg_1631_);
return v___x_1693_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_1694_, lean_object* v_declHint_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_1694_, v_declHint_1695_, v___y_1696_);
lean_dec(v___y_1696_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(lean_object* v_msg_1699_, lean_object* v_declHint_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1706_; lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1716_; 
v___x_1706_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_1699_, v_declHint_1700_, v___y_1704_);
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1709_ = v___x_1706_;
v_isShared_1710_ = v_isSharedCheck_1716_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1706_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1716_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1711_ = l_Lean_unknownIdentifierMessageTag;
v___x_1712_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1711_);
lean_ctor_set(v___x_1712_, 1, v_a_1707_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v___x_1712_);
v___x_1714_ = v___x_1709_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1717_, lean_object* v_declHint_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(v_msg_1717_, v_declHint_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(lean_object* v_ref_1725_, lean_object* v_msg_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v_toCold_1732_; lean_object* v_currRecDepth_1733_; lean_object* v_ref_1734_; uint16_t v_optionFlags_1735_; uint8_t v_suppressElabErrors_1736_; uint8_t v_isRecordingDeps_1737_; lean_object* v_ref_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v_toCold_1732_ = lean_ctor_get(v___y_1729_, 0);
v_currRecDepth_1733_ = lean_ctor_get(v___y_1729_, 1);
v_ref_1734_ = lean_ctor_get(v___y_1729_, 2);
v_optionFlags_1735_ = lean_ctor_get_uint16(v___y_1729_, sizeof(void*)*3);
v_suppressElabErrors_1736_ = lean_ctor_get_uint8(v___y_1729_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1737_ = lean_ctor_get_uint8(v___y_1729_, sizeof(void*)*3 + 3);
v_ref_1738_ = l_Lean_replaceRef(v_ref_1725_, v_ref_1734_);
lean_inc(v_currRecDepth_1733_);
lean_inc_ref(v_toCold_1732_);
v___x_1739_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1739_, 0, v_toCold_1732_);
lean_ctor_set(v___x_1739_, 1, v_currRecDepth_1733_);
lean_ctor_set(v___x_1739_, 2, v_ref_1738_);
lean_ctor_set_uint16(v___x_1739_, sizeof(void*)*3, v_optionFlags_1735_);
lean_ctor_set_uint8(v___x_1739_, sizeof(void*)*3 + 2, v_suppressElabErrors_1736_);
lean_ctor_set_uint8(v___x_1739_, sizeof(void*)*3 + 3, v_isRecordingDeps_1737_);
v___x_1740_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v_msg_1726_, v___y_1727_, v___y_1728_, v___x_1739_, v___y_1730_);
lean_dec_ref_known(v___x_1739_, 3);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_ref_1741_, lean_object* v_msg_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_1741_, v_msg_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v_ref_1741_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(lean_object* v_ref_1749_, lean_object* v_msg_1750_, lean_object* v_declHint_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v___x_1757_; lean_object* v_a_1758_; lean_object* v___x_1759_; 
v___x_1757_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(v_msg_1750_, v_declHint_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref(v___x_1757_);
v___x_1759_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_1749_, v_a_1758_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg___boxed(lean_object* v_ref_1760_, lean_object* v_msg_1761_, lean_object* v_declHint_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_1760_, v_msg_1761_, v_declHint_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v_ref_1760_);
return v_res_1768_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__0));
v___x_1771_ = l_Lean_stringToMessageData(v___x_1770_);
return v___x_1771_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__2));
v___x_1774_ = l_Lean_stringToMessageData(v___x_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_ref_1775_, lean_object* v_constName_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v___x_1782_; uint8_t v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1782_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1);
v___x_1783_ = 0;
lean_inc(v_constName_1776_);
v___x_1784_ = l_Lean_MessageData_ofConstName(v_constName_1776_, v___x_1783_);
v___x_1785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1782_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
v___x_1786_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3);
v___x_1787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1785_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_1775_, v___x_1787_, v_constName_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v_ref_1789_, lean_object* v_constName_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1789_, v_constName_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v_ref_1789_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(lean_object* v_constName_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v_ref_1803_; lean_object* v___x_1804_; 
v_ref_1803_ = lean_ctor_get(v___y_1800_, 2);
v___x_1804_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1803_, v_constName_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_constName_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(lean_object* v_constName_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; lean_object* v_env_1819_; uint8_t v___x_1820_; lean_object* v___x_1821_; 
v___x_1818_ = lean_st_ref_get(v___y_1816_);
v_env_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc_ref(v_env_1819_);
lean_dec(v___x_1818_);
v___x_1820_ = 0;
lean_inc(v_constName_1812_);
v___x_1821_ = l_Lean_Environment_find_x3f(v_env_1819_, v_constName_1812_, v___x_1820_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
return v___x_1822_;
}
else
{
lean_object* v_val_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_dec(v_constName_1812_);
v_val_1823_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1821_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_val_1823_);
lean_dec(v___x_1821_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set_tag(v___x_1825_, 0);
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_val_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0___boxed(lean_object* v_constName_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(v_constName_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(lean_object* v_declName_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = lean_box(0);
lean_inc(v_declName_1838_);
v___x_1845_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(v_declName_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1871_; 
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1871_ == 0)
{
lean_object* v_unused_1872_; 
v_unused_1872_ = lean_ctor_get(v___x_1845_, 0);
lean_dec(v_unused_1872_);
v___x_1847_ = v___x_1845_;
v_isShared_1848_ = v_isSharedCheck_1871_;
goto v_resetjp_1846_;
}
else
{
lean_dec(v___x_1845_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1871_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1849_; lean_object* v_env_1850_; lean_object* v___x_1851_; 
v___x_1849_ = lean_st_ref_get(v___y_1842_);
v_env_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc_ref(v_env_1850_);
lean_dec(v___x_1849_);
v___x_1851_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1850_, v_declName_1838_);
lean_dec(v_declName_1838_);
lean_dec_ref(v_env_1850_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1852_ = lean_box(0);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v___x_1852_);
v___x_1854_ = v___x_1847_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
else
{
lean_object* v_val_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1870_; 
v_val_1856_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1858_ = v___x_1851_;
v_isShared_1859_ = v_isSharedCheck_1870_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_val_1856_);
lean_dec(v___x_1851_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1870_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; lean_object* v_env_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1860_ = lean_st_ref_get(v___y_1842_);
v_env_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc_ref(v_env_1861_);
lean_dec(v___x_1860_);
v___x_1862_ = l_Lean_Environment_allImportedModuleNames(v_env_1861_);
lean_dec_ref(v_env_1861_);
v___x_1863_ = lean_array_get(v___x_1844_, v___x_1862_, v_val_1856_);
lean_dec(v_val_1856_);
lean_dec_ref(v___x_1862_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1863_);
v___x_1865_ = v___x_1858_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_object* v___x_1867_; 
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v___x_1865_);
v___x_1867_ = v___x_1847_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec(v_declName_1838_);
v_a_1873_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1845_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1845_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0___boxed(lean_object* v_declName_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(v_declName_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(lean_object* v_init_1888_, lean_object* v_x_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
if (lean_obj_tag(v_x_1889_) == 0)
{
lean_object* v_k_1895_; lean_object* v_l_1896_; lean_object* v_r_1897_; lean_object* v___x_1898_; 
v_k_1895_ = lean_ctor_get(v_x_1889_, 1);
lean_inc(v_k_1895_);
v_l_1896_ = lean_ctor_get(v_x_1889_, 3);
lean_inc(v_l_1896_);
v_r_1897_ = lean_ctor_get(v_x_1889_, 4);
lean_inc(v_r_1897_);
lean_dec_ref_known(v_x_1889_, 5);
v___x_1898_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v_init_1888_, v_l_1896_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1900_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___x_1898_, 1);
v___x_1900_ = l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(v_k_1895_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1902_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
lean_dec_ref_known(v___x_1900_, 1);
v___x_1902_ = lean_array_push(v_a_1899_, v_a_1901_);
v_init_1888_ = v___x_1902_;
v_x_1889_ = v_r_1897_;
goto _start;
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec(v_a_1899_);
lean_dec(v_r_1897_);
v_a_1904_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1900_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1900_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
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
lean_dec(v_r_1897_);
lean_dec(v_k_1895_);
return v___x_1898_;
}
}
else
{
lean_object* v___x_1912_; 
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v_init_1888_);
return v___x_1912_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3___boxed(lean_object* v_init_1913_, lean_object* v_x_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v_init_1913_, v_x_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
return v_res_1920_;
}
}
static lean_object* _init_l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1(void){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1922_ = l_Lean_NameSet_empty;
v___x_1923_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1);
v___x_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
lean_ctor_set(v___x_1924_, 1, v___x_1922_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(lean_object* v_pre_1925_, lean_object* v_type_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_){
_start:
{
lean_object* v___f_1932_; lean_object* v___y_1934_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___f_1932_ = ((lean_object*)(l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0));
v___x_1940_ = lean_unsigned_to_nat(0u);
v___x_1941_ = lean_obj_once(&l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1, &l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1_once, _init_l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1);
v___x_1942_ = lean_st_mk_ref(v___x_1941_);
lean_inc_ref(v_type_1926_);
v___x_1943_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(v_type_1926_, v___x_1942_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v_a_1948_; lean_object* v_consts_1949_; lean_object* v___x_1950_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1962_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref_known(v___x_1943_, 1);
v___x_1945_ = lean_st_ref_get(v___x_1942_);
lean_dec(v___x_1942_);
v___x_1946_ = lean_string_append(v_pre_1925_, v_a_1944_);
lean_dec(v_a_1944_);
v___x_1947_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v_a_1930_);
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref(v___x_1947_);
v_consts_1949_ = lean_ctor_get(v___x_1945_, 1);
lean_inc(v_consts_1949_);
lean_dec(v___x_1945_);
v___x_1950_ = l_Lean_Name_getRoot(v_a_1948_);
lean_dec(v_a_1948_);
if (lean_obj_tag(v_consts_1949_) == 0)
{
lean_object* v_size_1979_; 
v_size_1979_ = lean_ctor_get(v_consts_1949_, 0);
lean_inc(v_size_1979_);
v___y_1962_ = v_size_1979_;
goto v___jp_1961_;
}
else
{
v___y_1962_ = v___x_1940_;
goto v___jp_1961_;
}
v___jp_1951_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(v___x_1950_);
v___x_1953_ = lean_string_append(v___x_1946_, v___x_1952_);
lean_dec_ref(v___x_1952_);
v___y_1934_ = v___x_1953_;
goto v___jp_1933_;
}
v___jp_1954_:
{
uint8_t v___x_1957_; 
v___x_1957_ = lean_nat_dec_lt(v___x_1940_, v___y_1956_);
if (v___x_1957_ == 0)
{
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
goto v___jp_1951_;
}
else
{
if (v___x_1957_ == 0)
{
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
goto v___jp_1951_;
}
else
{
size_t v___x_1958_; size_t v___x_1959_; uint8_t v___x_1960_; 
v___x_1958_ = ((size_t)0ULL);
v___x_1959_ = lean_usize_of_nat(v___y_1956_);
lean_dec(v___y_1956_);
lean_inc(v___x_1950_);
v___x_1960_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(v___x_1950_, v___y_1955_, v___x_1958_, v___x_1959_);
lean_dec_ref(v___y_1955_);
if (v___x_1960_ == 0)
{
goto v___jp_1951_;
}
else
{
lean_dec(v___x_1950_);
v___y_1934_ = v___x_1946_;
goto v___jp_1933_;
}
}
}
}
v___jp_1961_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = lean_mk_empty_array_with_capacity(v___y_1962_);
lean_dec(v___y_1962_);
v___x_1964_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v___x_1963_, v_consts_1949_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1966_; uint8_t v___x_1967_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
lean_dec_ref_known(v___x_1964_, 1);
v___x_1966_ = lean_array_get_size(v_a_1965_);
v___x_1967_ = lean_nat_dec_lt(v___x_1940_, v___x_1966_);
if (v___x_1967_ == 0)
{
v___y_1955_ = v_a_1965_;
v___y_1956_ = v___x_1966_;
goto v___jp_1954_;
}
else
{
if (v___x_1967_ == 0)
{
v___y_1955_ = v_a_1965_;
v___y_1956_ = v___x_1966_;
goto v___jp_1954_;
}
else
{
size_t v___x_1968_; size_t v___x_1969_; uint8_t v___x_1970_; 
v___x_1968_ = ((size_t)0ULL);
v___x_1969_ = lean_usize_of_nat(v___x_1966_);
v___x_1970_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(v_a_1965_, v___x_1968_, v___x_1969_);
if (v___x_1970_ == 0)
{
v___y_1955_ = v_a_1965_;
v___y_1956_ = v___x_1966_;
goto v___jp_1954_;
}
else
{
lean_dec(v_a_1965_);
lean_dec(v___x_1950_);
v___y_1934_ = v___x_1946_;
goto v___jp_1933_;
}
}
}
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec(v___x_1950_);
lean_dec_ref(v___x_1946_);
lean_dec_ref(v_type_1926_);
v_a_1971_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1964_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1964_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec(v___x_1942_);
lean_dec_ref(v_type_1926_);
lean_dec_ref(v_pre_1925_);
v_a_1980_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1943_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1943_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
v___jp_1933_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1935_ = lean_box(0);
v___x_1936_ = l_Lean_Name_str___override(v___x_1935_, v___y_1934_);
v___x_1937_ = lean_find_expr(v___f_1932_, v_type_1926_);
lean_dec_ref(v_type_1926_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v___x_1938_; 
v___x_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1936_);
return v___x_1938_;
}
else
{
lean_object* v___x_1939_; 
lean_dec_ref_known(v___x_1937_, 1);
v___x_1939_ = l_Lean_Core_mkFreshUserName(v___x_1936_, v_a_1929_, v_a_1930_);
return v___x_1939_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___boxed(lean_object* v_pre_1988_, lean_object* v_type_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(v_pre_1988_, v_type_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
lean_dec(v_a_1993_);
lean_dec_ref(v_a_1992_);
lean_dec(v_a_1991_);
lean_dec_ref(v_a_1990_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1996_, lean_object* v_constName_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_2004_, lean_object* v_constName_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3(v_00_u03b1_2004_, v_constName_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b1_2012_, lean_object* v_ref_2013_, lean_object* v_constName_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v___x_2020_; 
v___x_2020_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_2013_, v_constName_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_00_u03b1_2021_, lean_object* v_ref_2022_, lean_object* v_constName_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7(v_00_u03b1_2021_, v_ref_2022_, v_constName_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v_ref_2022_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8(lean_object* v_00_u03b1_2030_, lean_object* v_ref_2031_, lean_object* v_msg_2032_, lean_object* v_declHint_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_2031_, v_msg_2032_, v_declHint_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___boxed(lean_object* v_00_u03b1_2040_, lean_object* v_ref_2041_, lean_object* v_msg_2042_, lean_object* v_declHint_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8(v_00_u03b1_2040_, v_ref_2041_, v_msg_2042_, v_declHint_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v_ref_2041_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10(lean_object* v_msg_2050_, lean_object* v_declHint_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_2050_, v_declHint_2051_, v___y_2055_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_2058_, lean_object* v_declHint_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10(v_msg_2058_, v_declHint_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_2066_, lean_object* v_ref_2067_, lean_object* v_msg_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v___x_2074_; 
v___x_2074_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_2067_, v_msg_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_2075_, lean_object* v_ref_2076_, lean_object* v_msg_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10(v_00_u03b1_2075_, v_ref_2076_, v_msg_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v_ref_2076_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg(lean_object* v_a_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v___x_2092_; 
v___x_2092_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg___boxed(lean_object* v_a_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg(v_a_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0(lean_object* v_00_u03b1_2102_, lean_object* v_a_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___boxed(lean_object* v_00_u03b1_2112_, lean_object* v_a_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0(v_00_u03b1_2112_, v_a_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0(lean_object* v_type_2122_, lean_object* v_binds_2123_, lean_object* v_pre_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_Elab_Term_elabType(v_type_2122_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; uint8_t v___x_2134_; uint8_t v___x_2135_; uint8_t v___x_2136_; lean_object* v___x_2137_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v___x_2134_ = 0;
v___x_2135_ = 1;
v___x_2136_ = 1;
v___x_2137_ = l_Lean_Meta_mkForallFVars(v_binds_2123_, v_a_2133_, v___x_2134_, v___x_2135_, v___x_2135_, v___x_2136_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2139_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v___x_2139_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(v_pre_2124_, v_a_2138_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
return v___x_2139_;
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec_ref(v_pre_2124_);
v_a_2140_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2137_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2137_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec_ref(v_pre_2124_);
v_a_2148_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2132_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2132_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0___boxed(lean_object* v_type_2156_, lean_object* v_binds_2157_, lean_object* v_pre_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0(v_type_2156_, v_binds_2157_, v_pre_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec_ref(v_binds_2157_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1(lean_object* v_type_2167_, lean_object* v_pre_2168_, lean_object* v_binds_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___f_2177_; lean_object* v___x_2178_; 
v___f_2177_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2177_, 0, v_type_2167_);
lean_closure_set(v___f_2177_, 1, v_binds_2169_);
lean_closure_set(v___f_2177_, 2, v_pre_2168_);
v___x_2178_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_2177_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1___boxed(lean_object* v_type_2179_, lean_object* v_pre_2180_, lean_object* v_binds_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1(v_type_2179_, v_pre_2180_, v_binds_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3(lean_object* v_env_2190_, lean_object* v___x_2191_, lean_object* v_currNamespace_2192_, lean_object* v_openDecls_2193_, lean_object* v_n_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = l_Lean_ResolveName_resolveGlobalName(v_env_2190_, v___x_2191_, v_currNamespace_2192_, v_openDecls_2193_, v_n_2194_);
v___x_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
lean_ctor_set(v___x_2198_, 1, v___y_2196_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3___boxed(lean_object* v_env_2199_, lean_object* v___x_2200_, lean_object* v_currNamespace_2201_, lean_object* v_openDecls_2202_, lean_object* v_n_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3(v_env_2199_, v___x_2200_, v_currNamespace_2201_, v_openDecls_2202_, v_n_2203_, v___y_2204_, v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec_ref(v___x_2200_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(lean_object* v_x_2207_, lean_object* v___y_2208_){
_start:
{
if (lean_obj_tag(v_x_2207_) == 0)
{
lean_object* v_a_2209_; lean_object* v___x_2210_; 
v_a_2209_ = lean_ctor_get(v_x_2207_, 0);
lean_inc(v_a_2209_);
v___x_2210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2210_, 0, v_a_2209_);
lean_ctor_set(v___x_2210_, 1, v___y_2208_);
return v___x_2210_;
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2212_; 
v_a_2211_ = lean_ctor_get(v_x_2207_, 0);
lean_inc(v_a_2211_);
v___x_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2212_, 0, v_a_2211_);
lean_ctor_set(v___x_2212_, 1, v___y_2208_);
return v___x_2212_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg___boxed(lean_object* v_x_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v_x_2213_, v___y_2214_);
lean_dec_ref(v_x_2213_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1(lean_object* v_env_2216_, lean_object* v_stx_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2216_, v_stx_2217_, v___y_2218_, v___y_2219_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
if (lean_obj_tag(v_a_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2230_; 
v_a_2222_ = lean_ctor_get(v___x_2220_, 1);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; 
v_unused_2231_ = lean_ctor_get(v___x_2220_, 0);
lean_dec(v_unused_2231_);
v___x_2224_ = v___x_2220_;
v_isShared_2225_ = v_isSharedCheck_2230_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2220_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2230_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2226_ = lean_box(0);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v___x_2226_);
v___x_2228_ = v___x_2224_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2226_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_a_2222_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
else
{
lean_object* v_val_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2260_; 
v_val_2232_ = lean_ctor_get(v_a_2221_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v_a_2221_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2234_ = v_a_2221_;
v_isShared_2235_ = v_isSharedCheck_2260_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_val_2232_);
lean_dec(v_a_2221_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2260_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v_snd_2236_; 
v_snd_2236_ = lean_ctor_get(v_val_2232_, 1);
lean_inc(v_snd_2236_);
lean_dec(v_val_2232_);
if (lean_obj_tag(v_snd_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2246_; 
lean_del_object(v___x_2234_);
v_a_2237_ = lean_ctor_get(v___x_2220_, 1);
lean_inc(v_a_2237_);
lean_dec_ref_known(v___x_2220_, 2);
v_a_2238_ = lean_ctor_get(v_snd_2236_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_snd_2236_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2240_ = v_snd_2236_;
v_isShared_2241_ = v_isSharedCheck_2246_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v_snd_2236_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2246_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v___x_2243_, v_a_2237_);
lean_dec_ref(v___x_2243_);
return v___x_2244_;
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2259_; 
v_a_2247_ = lean_ctor_get(v___x_2220_, 1);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2220_, 2);
v_a_2248_ = lean_ctor_get(v_snd_2236_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_snd_2236_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2250_ = v_snd_2236_;
v_isShared_2251_ = v_isSharedCheck_2259_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v_snd_2236_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2259_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v_a_2248_);
v___x_2253_ = v___x_2234_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
lean_object* v___x_2255_; 
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 0, v___x_2253_);
v___x_2255_ = v___x_2250_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2253_);
v___x_2255_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v___x_2255_, v_a_2247_);
lean_dec_ref(v___x_2255_);
return v___x_2256_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2261_; lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
v_a_2261_ = lean_ctor_get(v___x_2220_, 0);
v_a_2262_ = lean_ctor_get(v___x_2220_, 1);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2220_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_inc(v_a_2261_);
lean_dec(v___x_2220_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2261_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1___boxed(lean_object* v_env_2270_, lean_object* v_stx_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1(v_env_2270_, v_stx_2271_, v___y_2272_, v___y_2273_);
lean_dec_ref(v___y_2272_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0(lean_object* v_env_2275_, lean_object* v_declName_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
uint8_t v___x_2279_; lean_object* v_env_2280_; lean_object* v___x_2281_; uint8_t v___x_2282_; uint8_t v___x_2283_; 
v___x_2279_ = 0;
v_env_2280_ = l_Lean_Environment_setExporting(v_env_2275_, v___x_2279_);
lean_inc(v_declName_2276_);
v___x_2281_ = l_Lean_mkPrivateName(v_env_2280_, v_declName_2276_);
v___x_2282_ = 1;
lean_inc_ref(v_env_2280_);
v___x_2283_ = l_Lean_Environment_contains(v_env_2280_, v___x_2281_, v___x_2282_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; uint8_t v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2284_ = l_Lean_privateToUserName(v_declName_2276_);
v___x_2285_ = l_Lean_Environment_contains(v_env_2280_, v___x_2284_, v___x_2282_);
v___x_2286_ = lean_box(v___x_2285_);
v___x_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
lean_ctor_set(v___x_2287_, 1, v___y_2278_);
return v___x_2287_;
}
else
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
lean_dec_ref(v_env_2280_);
lean_dec(v_declName_2276_);
v___x_2288_ = lean_box(v___x_2283_);
v___x_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
lean_ctor_set(v___x_2289_, 1, v___y_2278_);
return v___x_2289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0___boxed(lean_object* v_env_2290_, lean_object* v_declName_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0(v_env_2290_, v_declName_2291_, v___y_2292_, v___y_2293_);
lean_dec_ref(v___y_2292_);
return v_res_2294_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17(lean_object* v_opts_2295_, lean_object* v_opt_2296_){
_start:
{
lean_object* v_name_2297_; lean_object* v_defValue_2298_; lean_object* v_map_2299_; lean_object* v___x_2300_; 
v_name_2297_ = lean_ctor_get(v_opt_2296_, 0);
v_defValue_2298_ = lean_ctor_get(v_opt_2296_, 1);
v_map_2299_ = lean_ctor_get(v_opts_2295_, 0);
v___x_2300_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2299_, v_name_2297_);
if (lean_obj_tag(v___x_2300_) == 0)
{
uint8_t v___x_2301_; 
v___x_2301_ = lean_unbox(v_defValue_2298_);
return v___x_2301_;
}
else
{
lean_object* v_val_2302_; 
v_val_2302_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_val_2302_);
lean_dec_ref_known(v___x_2300_, 1);
if (lean_obj_tag(v_val_2302_) == 1)
{
uint8_t v_v_2303_; 
v_v_2303_ = lean_ctor_get_uint8(v_val_2302_, 0);
lean_dec_ref_known(v_val_2302_, 0);
return v_v_2303_;
}
else
{
uint8_t v___x_2304_; 
lean_dec(v_val_2302_);
v___x_2304_ = lean_unbox(v_defValue_2298_);
return v___x_2304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17___boxed(lean_object* v_opts_2305_, lean_object* v_opt_2306_){
_start:
{
uint8_t v_res_2307_; lean_object* v_r_2308_; 
v_res_2307_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17(v_opts_2305_, v_opt_2306_);
lean_dec_ref(v_opt_2306_);
lean_dec_ref(v_opts_2305_);
v_r_2308_ = lean_box(v_res_2307_);
return v_r_2308_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0(void){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = lean_box(1);
v___x_2310_ = l_Lean_MessageData_ofFormat(v___x_2309_);
return v___x_2310_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__2));
v___x_2315_ = l_Lean_MessageData_ofFormat(v___x_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18(lean_object* v_x_2316_, lean_object* v_x_2317_){
_start:
{
if (lean_obj_tag(v_x_2317_) == 0)
{
return v_x_2316_;
}
else
{
lean_object* v_head_2318_; lean_object* v_tail_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2341_; 
v_head_2318_ = lean_ctor_get(v_x_2317_, 0);
v_tail_2319_ = lean_ctor_get(v_x_2317_, 1);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_x_2317_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2321_ = v_x_2317_;
v_isShared_2322_ = v_isSharedCheck_2341_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_tail_2319_);
lean_inc(v_head_2318_);
lean_dec(v_x_2317_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2341_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v_before_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2339_; 
v_before_2323_ = lean_ctor_get(v_head_2318_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v_head_2318_);
if (v_isSharedCheck_2339_ == 0)
{
lean_object* v_unused_2340_; 
v_unused_2340_ = lean_ctor_get(v_head_2318_, 1);
lean_dec(v_unused_2340_);
v___x_2325_ = v_head_2318_;
v_isShared_2326_ = v_isSharedCheck_2339_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_before_2323_);
lean_dec(v_head_2318_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2339_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v___x_2329_; 
v___x_2327_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0);
if (v_isShared_2326_ == 0)
{
lean_ctor_set_tag(v___x_2325_, 7);
lean_ctor_set(v___x_2325_, 1, v___x_2327_);
lean_ctor_set(v___x_2325_, 0, v_x_2316_);
v___x_2329_ = v___x_2325_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_x_2316_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v___x_2327_);
v___x_2329_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
lean_object* v___x_2330_; lean_object* v___x_2332_; 
v___x_2330_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3);
if (v_isShared_2322_ == 0)
{
lean_ctor_set_tag(v___x_2321_, 7);
lean_ctor_set(v___x_2321_, 1, v___x_2330_);
lean_ctor_set(v___x_2321_, 0, v___x_2329_);
v___x_2332_ = v___x_2321_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2329_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2333_ = l_Lean_MessageData_ofSyntax(v_before_2323_);
v___x_2334_ = l_Lean_indentD(v___x_2333_);
v___x_2335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2332_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
v_x_2316_ = v___x_2335_;
v_x_2317_ = v_tail_2319_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2(void){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__1));
v___x_2346_ = l_Lean_MessageData_ofFormat(v___x_2345_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(lean_object* v_msgData_2347_, lean_object* v_macroStack_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; uint8_t v___x_2353_; 
v___x_2351_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2349_);
v___x_2352_ = l_Lean_Elab_pp_macroStack;
v___x_2353_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17(v___x_2351_, v___x_2352_);
lean_dec_ref(v___x_2351_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; 
lean_dec(v_macroStack_2348_);
v___x_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2354_, 0, v_msgData_2347_);
return v___x_2354_;
}
else
{
if (lean_obj_tag(v_macroStack_2348_) == 0)
{
lean_object* v___x_2355_; 
v___x_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2355_, 0, v_msgData_2347_);
return v___x_2355_;
}
else
{
lean_object* v_head_2356_; lean_object* v_after_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2372_; 
v_head_2356_ = lean_ctor_get(v_macroStack_2348_, 0);
lean_inc(v_head_2356_);
v_after_2357_ = lean_ctor_get(v_head_2356_, 1);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_head_2356_);
if (v_isSharedCheck_2372_ == 0)
{
lean_object* v_unused_2373_; 
v_unused_2373_ = lean_ctor_get(v_head_2356_, 0);
lean_dec(v_unused_2373_);
v___x_2359_ = v_head_2356_;
v_isShared_2360_ = v_isSharedCheck_2372_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_after_2357_);
lean_dec(v_head_2356_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2372_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2361_; lean_object* v___x_2363_; 
v___x_2361_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0);
if (v_isShared_2360_ == 0)
{
lean_ctor_set_tag(v___x_2359_, 7);
lean_ctor_set(v___x_2359_, 1, v___x_2361_);
lean_ctor_set(v___x_2359_, 0, v_msgData_2347_);
v___x_2363_ = v___x_2359_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_msgData_2347_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v_msgData_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2364_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2);
v___x_2365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2363_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
v___x_2366_ = l_Lean_MessageData_ofSyntax(v_after_2357_);
v___x_2367_ = l_Lean_indentD(v___x_2366_);
v_msgData_2368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2368_, 0, v___x_2365_);
lean_ctor_set(v_msgData_2368_, 1, v___x_2367_);
v___x_2369_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18(v_msgData_2368_, v_macroStack_2348_);
v___x_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
return v___x_2370_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___boxed(lean_object* v_msgData_2374_, lean_object* v_macroStack_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_msgData_2374_, v_macroStack_2375_, v___y_2376_);
lean_dec_ref(v___y_2376_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(lean_object* v_msg_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v_ref_2387_; lean_object* v_macroStack_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v_a_2391_; lean_object* v___x_2392_; lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2401_; 
v_ref_2387_ = lean_ctor_get(v___y_2384_, 2);
v_macroStack_2388_ = lean_ctor_get(v___y_2380_, 1);
v___x_2389_ = l_Lean_Elab_getBetterRef(v_ref_2387_, v_macroStack_2388_);
v___x_2390_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msg_2379_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref(v___x_2390_);
lean_inc(v_macroStack_2388_);
v___x_2392_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_a_2391_, v_macroStack_2388_, v___y_2384_);
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2395_ = v___x_2392_;
v_isShared_2396_ = v_isSharedCheck_2401_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2392_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2401_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2397_; lean_object* v___x_2399_; 
v___x_2397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2389_);
lean_ctor_set(v___x_2397_, 1, v_a_2393_);
if (v_isShared_2396_ == 0)
{
lean_ctor_set_tag(v___x_2395_, 1);
lean_ctor_set(v___x_2395_, 0, v___x_2397_);
v___x_2399_ = v___x_2395_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg___boxed(lean_object* v_msg_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(lean_object* v_ref_2411_, lean_object* v_msg_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v_toCold_2420_; lean_object* v_currRecDepth_2421_; lean_object* v_ref_2422_; uint16_t v_optionFlags_2423_; uint8_t v_suppressElabErrors_2424_; uint8_t v_isRecordingDeps_2425_; lean_object* v_ref_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v_toCold_2420_ = lean_ctor_get(v___y_2417_, 0);
v_currRecDepth_2421_ = lean_ctor_get(v___y_2417_, 1);
v_ref_2422_ = lean_ctor_get(v___y_2417_, 2);
v_optionFlags_2423_ = lean_ctor_get_uint16(v___y_2417_, sizeof(void*)*3);
v_suppressElabErrors_2424_ = lean_ctor_get_uint8(v___y_2417_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2425_ = lean_ctor_get_uint8(v___y_2417_, sizeof(void*)*3 + 3);
v_ref_2426_ = l_Lean_replaceRef(v_ref_2411_, v_ref_2422_);
lean_inc(v_currRecDepth_2421_);
lean_inc_ref(v_toCold_2420_);
v___x_2427_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2427_, 0, v_toCold_2420_);
lean_ctor_set(v___x_2427_, 1, v_currRecDepth_2421_);
lean_ctor_set(v___x_2427_, 2, v_ref_2426_);
lean_ctor_set_uint16(v___x_2427_, sizeof(void*)*3, v_optionFlags_2423_);
lean_ctor_set_uint8(v___x_2427_, sizeof(void*)*3 + 2, v_suppressElabErrors_2424_);
lean_ctor_set_uint8(v___x_2427_, sizeof(void*)*3 + 3, v_isRecordingDeps_2425_);
v___x_2428_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___x_2427_, v___y_2418_);
lean_dec_ref_known(v___x_2427_, 3);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg___boxed(lean_object* v_ref_2429_, lean_object* v_msg_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_ref_2429_, v_msg_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v_ref_2429_);
return v_res_2438_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2439_; double v___x_2440_; 
v___x_2439_ = lean_unsigned_to_nat(0u);
v___x_2440_ = lean_float_of_nat(v___x_2439_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(lean_object* v_cls_2443_, lean_object* v_msg_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v_ref_2450_; lean_object* v___x_2451_; lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2497_; 
v_ref_2450_ = lean_ctor_get(v___y_2447_, 2);
v___x_2451_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msg_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2454_ = v___x_2451_;
v_isShared_2455_ = v_isSharedCheck_2497_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2451_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2497_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2456_; lean_object* v_traceState_2457_; lean_object* v_env_2458_; lean_object* v_nextMacroScope_2459_; lean_object* v_ngen_2460_; lean_object* v_auxDeclNGen_2461_; lean_object* v_cache_2462_; lean_object* v_recordedDeps_2463_; lean_object* v_messages_2464_; lean_object* v_infoState_2465_; lean_object* v_snapshotTasks_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2496_; 
v___x_2456_ = lean_st_ref_take(v___y_2448_);
v_traceState_2457_ = lean_ctor_get(v___x_2456_, 4);
v_env_2458_ = lean_ctor_get(v___x_2456_, 0);
v_nextMacroScope_2459_ = lean_ctor_get(v___x_2456_, 1);
v_ngen_2460_ = lean_ctor_get(v___x_2456_, 2);
v_auxDeclNGen_2461_ = lean_ctor_get(v___x_2456_, 3);
v_cache_2462_ = lean_ctor_get(v___x_2456_, 5);
v_recordedDeps_2463_ = lean_ctor_get(v___x_2456_, 6);
v_messages_2464_ = lean_ctor_get(v___x_2456_, 7);
v_infoState_2465_ = lean_ctor_get(v___x_2456_, 8);
v_snapshotTasks_2466_ = lean_ctor_get(v___x_2456_, 9);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2468_ = v___x_2456_;
v_isShared_2469_ = v_isSharedCheck_2496_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_snapshotTasks_2466_);
lean_inc(v_infoState_2465_);
lean_inc(v_messages_2464_);
lean_inc(v_recordedDeps_2463_);
lean_inc(v_cache_2462_);
lean_inc(v_traceState_2457_);
lean_inc(v_auxDeclNGen_2461_);
lean_inc(v_ngen_2460_);
lean_inc(v_nextMacroScope_2459_);
lean_inc(v_env_2458_);
lean_dec(v___x_2456_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2496_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
uint64_t v_tid_2470_; lean_object* v_traces_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2495_; 
v_tid_2470_ = lean_ctor_get_uint64(v_traceState_2457_, sizeof(void*)*1);
v_traces_2471_ = lean_ctor_get(v_traceState_2457_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v_traceState_2457_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2473_ = v_traceState_2457_;
v_isShared_2474_ = v_isSharedCheck_2495_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_traces_2471_);
lean_dec(v_traceState_2457_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2495_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; double v___x_2477_; uint8_t v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2486_; 
v___x_2475_ = lean_box(0);
v___x_2476_ = lean_box(0);
v___x_2477_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0);
v___x_2478_ = 0;
v___x_2479_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_2480_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2480_, 0, v_cls_2443_);
lean_ctor_set(v___x_2480_, 1, v___x_2476_);
lean_ctor_set(v___x_2480_, 2, v___x_2479_);
lean_ctor_set_float(v___x_2480_, sizeof(void*)*3, v___x_2477_);
lean_ctor_set_float(v___x_2480_, sizeof(void*)*3 + 8, v___x_2477_);
lean_ctor_set_uint8(v___x_2480_, sizeof(void*)*3 + 16, v___x_2478_);
v___x_2481_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__1));
v___x_2482_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2480_);
lean_ctor_set(v___x_2482_, 1, v_a_2452_);
lean_ctor_set(v___x_2482_, 2, v___x_2481_);
lean_inc(v_ref_2450_);
v___x_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2483_, 0, v_ref_2450_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = l_Lean_PersistentArray_push___redArg(v_traces_2471_, v___x_2483_);
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 0, v___x_2484_);
v___x_2486_ = v___x_2473_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2484_);
lean_ctor_set_uint64(v_reuseFailAlloc_2494_, sizeof(void*)*1, v_tid_2470_);
v___x_2486_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
lean_object* v___x_2488_; 
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 4, v___x_2486_);
v___x_2488_ = v___x_2468_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_env_2458_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_nextMacroScope_2459_);
lean_ctor_set(v_reuseFailAlloc_2493_, 2, v_ngen_2460_);
lean_ctor_set(v_reuseFailAlloc_2493_, 3, v_auxDeclNGen_2461_);
lean_ctor_set(v_reuseFailAlloc_2493_, 4, v___x_2486_);
lean_ctor_set(v_reuseFailAlloc_2493_, 5, v_cache_2462_);
lean_ctor_set(v_reuseFailAlloc_2493_, 6, v_recordedDeps_2463_);
lean_ctor_set(v_reuseFailAlloc_2493_, 7, v_messages_2464_);
lean_ctor_set(v_reuseFailAlloc_2493_, 8, v_infoState_2465_);
lean_ctor_set(v_reuseFailAlloc_2493_, 9, v_snapshotTasks_2466_);
v___x_2488_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2489_; lean_object* v___x_2491_; 
v___x_2489_ = lean_st_ref_put(v___y_2448_, v___x_2488_);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 0, v___x_2475_);
v___x_2491_ = v___x_2454_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2475_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___boxed(lean_object* v_cls_2498_, lean_object* v_msg_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_2498_, v_msg_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(lean_object* v_as_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
if (lean_obj_tag(v_as_2509_) == 0)
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = lean_box(0);
v___x_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2517_);
return v___x_2518_;
}
else
{
lean_object* v_toCold_2519_; lean_object* v_options_2520_; uint8_t v_hasTrace_2521_; 
v_toCold_2519_ = lean_ctor_get(v___y_2514_, 0);
v_options_2520_ = lean_ctor_get(v_toCold_2519_, 2);
v_hasTrace_2521_ = lean_ctor_get_uint8(v_options_2520_, sizeof(void*)*1);
if (v_hasTrace_2521_ == 0)
{
lean_object* v_tail_2522_; 
v_tail_2522_ = lean_ctor_get(v_as_2509_, 1);
lean_inc(v_tail_2522_);
lean_dec_ref_known(v_as_2509_, 2);
v_as_2509_ = v_tail_2522_;
goto _start;
}
else
{
lean_object* v_head_2524_; lean_object* v_tail_2525_; lean_object* v_fst_2526_; lean_object* v_snd_2527_; lean_object* v_inheritedTraceOptions_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; 
v_head_2524_ = lean_ctor_get(v_as_2509_, 0);
lean_inc(v_head_2524_);
v_tail_2525_ = lean_ctor_get(v_as_2509_, 1);
lean_inc(v_tail_2525_);
lean_dec_ref_known(v_as_2509_, 2);
v_fst_2526_ = lean_ctor_get(v_head_2524_, 0);
lean_inc_n(v_fst_2526_, 2);
v_snd_2527_ = lean_ctor_get(v_head_2524_, 1);
lean_inc(v_snd_2527_);
lean_dec(v_head_2524_);
v_inheritedTraceOptions_2528_ = lean_ctor_get(v_toCold_2519_, 11);
v___x_2529_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__1));
v___x_2530_ = l_Lean_Name_append(v___x_2529_, v_fst_2526_);
v___x_2531_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2528_, v_options_2520_, v___x_2530_);
lean_dec(v___x_2530_);
if (v___x_2531_ == 0)
{
lean_dec(v_snd_2527_);
lean_dec(v_fst_2526_);
v_as_2509_ = v_tail_2525_;
goto _start;
}
else
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2533_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2533_, 0, v_snd_2527_);
v___x_2534_ = l_Lean_MessageData_ofFormat(v___x_2533_);
v___x_2535_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_fst_2526_, v___x_2534_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_dec_ref_known(v___x_2535_, 1);
v_as_2509_ = v_tail_2525_;
goto _start;
}
else
{
lean_dec(v_tail_2525_);
return v___x_2535_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___boxed(lean_object* v_as_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(v_as_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
return v_res_2545_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(lean_object* v_keys_2546_, lean_object* v_i_2547_, lean_object* v_k_2548_){
_start:
{
lean_object* v___x_2549_; uint8_t v___x_2550_; 
v___x_2549_ = lean_array_get_size(v_keys_2546_);
v___x_2550_ = lean_nat_dec_lt(v_i_2547_, v___x_2549_);
if (v___x_2550_ == 0)
{
lean_dec(v_i_2547_);
return v___x_2550_;
}
else
{
lean_object* v_k_x27_2551_; uint8_t v___x_2552_; 
v_k_x27_2551_ = lean_array_fget_borrowed(v_keys_2546_, v_i_2547_);
v___x_2552_ = l_Lean_instBEqExtraModUse_beq(v_k_2548_, v_k_x27_2551_);
if (v___x_2552_ == 0)
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = lean_unsigned_to_nat(1u);
v___x_2554_ = lean_nat_add(v_i_2547_, v___x_2553_);
lean_dec(v_i_2547_);
v_i_2547_ = v___x_2554_;
goto _start;
}
else
{
lean_dec(v_i_2547_);
return v___x_2550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg___boxed(lean_object* v_keys_2556_, lean_object* v_i_2557_, lean_object* v_k_2558_){
_start:
{
uint8_t v_res_2559_; lean_object* v_r_2560_; 
v_res_2559_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_keys_2556_, v_i_2557_, v_k_2558_);
lean_dec_ref(v_k_2558_);
lean_dec_ref(v_keys_2556_);
v_r_2560_ = lean_box(v_res_2559_);
return v_r_2560_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(lean_object* v_x_2561_, size_t v_x_2562_, lean_object* v_x_2563_){
_start:
{
if (lean_obj_tag(v_x_2561_) == 0)
{
lean_object* v_es_2564_; lean_object* v___x_2565_; size_t v___x_2566_; size_t v___x_2567_; lean_object* v_j_2568_; lean_object* v___x_2569_; 
v_es_2564_ = lean_ctor_get(v_x_2561_, 0);
v___x_2565_ = lean_box(2);
v___x_2566_ = ((size_t)31ULL);
v___x_2567_ = lean_usize_land(v_x_2562_, v___x_2566_);
v_j_2568_ = lean_usize_to_nat(v___x_2567_);
v___x_2569_ = lean_array_get_borrowed(v___x_2565_, v_es_2564_, v_j_2568_);
lean_dec(v_j_2568_);
switch(lean_obj_tag(v___x_2569_))
{
case 0:
{
lean_object* v_key_2570_; uint8_t v___x_2571_; 
v_key_2570_ = lean_ctor_get(v___x_2569_, 0);
v___x_2571_ = l_Lean_instBEqExtraModUse_beq(v_x_2563_, v_key_2570_);
return v___x_2571_;
}
case 1:
{
lean_object* v_node_2572_; size_t v___x_2573_; size_t v___x_2574_; 
v_node_2572_ = lean_ctor_get(v___x_2569_, 0);
v___x_2573_ = ((size_t)5ULL);
v___x_2574_ = lean_usize_shift_right(v_x_2562_, v___x_2573_);
v_x_2561_ = v_node_2572_;
v_x_2562_ = v___x_2574_;
goto _start;
}
default: 
{
uint8_t v___x_2576_; 
v___x_2576_ = 0;
return v___x_2576_;
}
}
}
else
{
lean_object* v_ks_2577_; lean_object* v___x_2578_; uint8_t v___x_2579_; 
v_ks_2577_ = lean_ctor_get(v_x_2561_, 0);
v___x_2578_ = lean_unsigned_to_nat(0u);
v___x_2579_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_ks_2577_, v___x_2578_, v_x_2563_);
return v___x_2579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_x_2580_, lean_object* v_x_2581_, lean_object* v_x_2582_){
_start:
{
size_t v_x_14877__boxed_2583_; uint8_t v_res_2584_; lean_object* v_r_2585_; 
v_x_14877__boxed_2583_ = lean_unbox_usize(v_x_2581_);
lean_dec(v_x_2581_);
v_res_2584_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_2580_, v_x_14877__boxed_2583_, v_x_2582_);
lean_dec_ref(v_x_2582_);
lean_dec_ref(v_x_2580_);
v_r_2585_ = lean_box(v_res_2584_);
return v_r_2585_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(lean_object* v_x_2586_, lean_object* v_x_2587_){
_start:
{
uint64_t v___x_2588_; size_t v___x_2589_; uint8_t v___x_2590_; 
v___x_2588_ = l_Lean_instHashableExtraModUse_hash(v_x_2587_);
v___x_2589_ = lean_uint64_to_usize(v___x_2588_);
v___x_2590_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_2586_, v___x_2589_, v_x_2587_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_x_2591_, lean_object* v_x_2592_){
_start:
{
uint8_t v_res_2593_; lean_object* v_r_2594_; 
v_res_2593_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v_x_2591_, v_x_2592_);
lean_dec_ref(v_x_2592_);
lean_dec_ref(v_x_2591_);
v_r_2594_ = lean_box(v_res_2593_);
return v_r_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___lam__0(lean_object* v___x_2595_, lean_object* v_entry_2596_, lean_object* v_s_2597_){
_start:
{
lean_object* v_addEntryFn_2598_; lean_object* v_importedEntries_2599_; lean_object* v_state_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2608_; 
v_addEntryFn_2598_ = lean_ctor_get(v___x_2595_, 3);
lean_inc(v_addEntryFn_2598_);
lean_dec_ref(v___x_2595_);
v_importedEntries_2599_ = lean_ctor_get(v_s_2597_, 0);
v_state_2600_ = lean_ctor_get(v_s_2597_, 1);
v_isSharedCheck_2608_ = !lean_is_exclusive(v_s_2597_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2602_ = v_s_2597_;
v_isShared_2603_ = v_isSharedCheck_2608_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_state_2600_);
lean_inc(v_importedEntries_2599_);
lean_dec(v_s_2597_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2608_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v_state_2604_; lean_object* v___x_2606_; 
v_state_2604_ = lean_apply_2(v_addEntryFn_2598_, v_state_2600_, v_entry_2596_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 1, v_state_2604_);
v___x_2606_ = v___x_2602_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_importedEntries_2599_);
lean_ctor_set(v_reuseFailAlloc_2607_, 1, v_state_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
return v___x_2610_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0);
v___x_2612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
lean_ctor_set(v___x_2612_, 1, v___x_2611_);
return v___x_2612_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0);
v___x_2614_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
lean_ctor_set(v___x_2614_, 2, v___x_2613_);
lean_ctor_set(v___x_2614_, 3, v___x_2613_);
lean_ctor_set(v___x_2614_, 4, v___x_2613_);
lean_ctor_set(v___x_2614_, 5, v___x_2613_);
return v___x_2614_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2615_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7(void){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6));
v___x_2621_ = l_Lean_stringToMessageData(v___x_2620_);
return v___x_2621_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9(void){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__8));
v___x_2624_ = l_Lean_stringToMessageData(v___x_2623_);
return v___x_2624_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10(void){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_2626_ = l_Lean_stringToMessageData(v___x_2625_);
return v___x_2626_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11(void){
_start:
{
lean_object* v_cls_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v_cls_2627_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5));
v___x_2628_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__1));
v___x_2629_ = l_Lean_Name_append(v___x_2628_, v_cls_2627_);
return v___x_2629_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12));
v___x_2632_ = l_Lean_stringToMessageData(v___x_2631_);
return v___x_2632_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15(void){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14));
v___x_2635_ = l_Lean_stringToMessageData(v___x_2634_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(lean_object* v_mod_2640_, uint8_t v_isMeta_2641_, lean_object* v_hint_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v_env_2684_; uint8_t v_isExporting_2685_; lean_object* v_entry_2686_; lean_object* v___x_2687_; lean_object* v_env_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; uint8_t v___x_2693_; 
v___x_2682_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3);
v___x_2683_ = lean_st_ref_get(v___y_2648_);
v_env_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc_ref(v_env_2684_);
lean_dec(v___x_2683_);
v_isExporting_2685_ = lean_ctor_get_uint8(v_env_2684_, sizeof(void*)*13);
lean_dec_ref(v_env_2684_);
lean_inc(v_mod_2640_);
v_entry_2686_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2686_, 0, v_mod_2640_);
lean_ctor_set_uint8(v_entry_2686_, sizeof(void*)*1, v_isExporting_2685_);
lean_ctor_set_uint8(v_entry_2686_, sizeof(void*)*1 + 1, v_isMeta_2641_);
v___x_2687_ = lean_st_ref_get(v___y_2648_);
v_env_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc_ref(v_env_2688_);
lean_dec(v___x_2687_);
v___x_2689_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2690_ = lean_box(1);
v___x_2691_ = lean_box(0);
v___x_2692_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2682_, v___x_2689_, v_env_2688_, v___x_2690_, v___x_2691_);
v___x_2693_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v___x_2692_, v_entry_2686_);
lean_dec(v___x_2692_);
if (v___x_2693_ == 0)
{
lean_object* v_toCold_2694_; lean_object* v_options_2695_; lean_object* v_inheritedTraceOptions_2696_; uint8_t v_hasTrace_2697_; lean_object* v___f_2698_; uint8_t v___x_2699_; lean_object* v___y_2701_; lean_object* v___y_2702_; 
v_toCold_2694_ = lean_ctor_get(v___y_2647_, 0);
v_options_2695_ = lean_ctor_get(v_toCold_2694_, 2);
v_inheritedTraceOptions_2696_ = lean_ctor_get(v_toCold_2694_, 11);
v_hasTrace_2697_ = lean_ctor_get_uint8(v_options_2695_, sizeof(void*)*1);
v___f_2698_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___lam__0), 3, 2);
lean_closure_set(v___f_2698_, 0, v___x_2689_);
lean_closure_set(v___f_2698_, 1, v_entry_2686_);
v___x_2699_ = 1;
if (v_hasTrace_2697_ == 0)
{
lean_dec(v_hint_2642_);
lean_dec(v_mod_2640_);
v___y_2701_ = v___y_2646_;
v___y_2702_ = v___y_2648_;
goto v___jp_2700_;
}
else
{
lean_object* v_cls_2729_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
v_cls_2729_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5));
v___x_2749_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11);
v___x_2750_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2696_, v_options_2695_, v___x_2749_);
if (v___x_2750_ == 0)
{
lean_dec(v_hint_2642_);
lean_dec(v_mod_2640_);
v___y_2701_ = v___y_2646_;
v___y_2702_ = v___y_2648_;
goto v___jp_2700_;
}
else
{
lean_object* v___x_2751_; lean_object* v___y_2753_; 
v___x_2751_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13);
if (v_isExporting_2685_ == 0)
{
lean_object* v___x_2760_; 
v___x_2760_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18));
v___y_2753_ = v___x_2760_;
goto v___jp_2752_;
}
else
{
lean_object* v___x_2761_; 
v___x_2761_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__19));
v___y_2753_ = v___x_2761_;
goto v___jp_2752_;
}
v___jp_2752_:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
lean_inc_ref(v___y_2753_);
v___x_2754_ = l_Lean_stringToMessageData(v___y_2753_);
v___x_2755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2751_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15);
v___x_2757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2755_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
if (v_isMeta_2641_ == 0)
{
lean_object* v___x_2758_; 
v___x_2758_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16));
v___y_2736_ = v___x_2757_;
v___y_2737_ = v___x_2758_;
goto v___jp_2735_;
}
else
{
lean_object* v___x_2759_; 
v___x_2759_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__17));
v___y_2736_ = v___x_2757_;
v___y_2737_ = v___x_2759_;
goto v___jp_2735_;
}
}
}
v___jp_2730_:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___y_2731_);
lean_ctor_set(v___x_2733_, 1, v___y_2732_);
v___x_2734_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_2729_, v___x_2733_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_dec_ref_known(v___x_2734_, 1);
v___y_2701_ = v___y_2646_;
v___y_2702_ = v___y_2648_;
goto v___jp_2700_;
}
else
{
lean_dec_ref(v___f_2698_);
return v___x_2734_;
}
}
v___jp_2735_:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; uint8_t v___x_2744_; 
lean_inc_ref(v___y_2737_);
v___x_2738_ = l_Lean_stringToMessageData(v___y_2737_);
v___x_2739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2739_, 0, v___y_2736_);
lean_ctor_set(v___x_2739_, 1, v___x_2738_);
v___x_2740_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7);
v___x_2741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2739_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v___x_2742_ = l_Lean_MessageData_ofName(v_mod_2640_);
v___x_2743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2741_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
v___x_2744_ = l_Lean_Name_isAnonymous(v_hint_2642_);
if (v___x_2744_ == 0)
{
lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2745_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9);
v___x_2746_ = l_Lean_MessageData_ofName(v_hint_2642_);
v___x_2747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2745_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___y_2731_ = v___x_2743_;
v___y_2732_ = v___x_2747_;
goto v___jp_2730_;
}
else
{
lean_object* v___x_2748_; 
lean_dec(v_hint_2642_);
v___x_2748_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10);
v___y_2731_ = v___x_2743_;
v___y_2732_ = v___x_2748_;
goto v___jp_2730_;
}
}
}
v___jp_2700_:
{
lean_object* v___x_2703_; lean_object* v_toEnvExtension_2704_; uint8_t v_logWrites_2705_; 
v___x_2703_ = lean_st_ref_take(v___y_2702_);
v_toEnvExtension_2704_ = lean_ctor_get(v___x_2689_, 0);
v_logWrites_2705_ = lean_ctor_get_uint8(v_toEnvExtension_2704_, sizeof(void*)*6);
if (v_logWrites_2705_ == 0)
{
lean_object* v_env_2706_; lean_object* v_nextMacroScope_2707_; lean_object* v_ngen_2708_; lean_object* v_auxDeclNGen_2709_; lean_object* v_traceState_2710_; lean_object* v_recordedDeps_2711_; lean_object* v_messages_2712_; lean_object* v_infoState_2713_; lean_object* v_snapshotTasks_2714_; lean_object* v_asyncMode_2715_; lean_object* v___x_2716_; 
v_env_2706_ = lean_ctor_get(v___x_2703_, 0);
lean_inc_ref(v_env_2706_);
v_nextMacroScope_2707_ = lean_ctor_get(v___x_2703_, 1);
lean_inc(v_nextMacroScope_2707_);
v_ngen_2708_ = lean_ctor_get(v___x_2703_, 2);
lean_inc_ref(v_ngen_2708_);
v_auxDeclNGen_2709_ = lean_ctor_get(v___x_2703_, 3);
lean_inc_ref(v_auxDeclNGen_2709_);
v_traceState_2710_ = lean_ctor_get(v___x_2703_, 4);
lean_inc_ref(v_traceState_2710_);
v_recordedDeps_2711_ = lean_ctor_get(v___x_2703_, 6);
lean_inc_ref(v_recordedDeps_2711_);
v_messages_2712_ = lean_ctor_get(v___x_2703_, 7);
lean_inc_ref(v_messages_2712_);
v_infoState_2713_ = lean_ctor_get(v___x_2703_, 8);
lean_inc_ref(v_infoState_2713_);
v_snapshotTasks_2714_ = lean_ctor_get(v___x_2703_, 9);
lean_inc_ref(v_snapshotTasks_2714_);
lean_dec(v___x_2703_);
v_asyncMode_2715_ = lean_ctor_get(v_toEnvExtension_2704_, 2);
lean_inc_ref(v_toEnvExtension_2704_);
v___x_2716_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2704_, v_env_2706_, v___f_2698_, v_asyncMode_2715_, v___x_2691_, v___x_2699_);
v___y_2651_ = v_nextMacroScope_2707_;
v___y_2652_ = v_traceState_2710_;
v___y_2653_ = v_auxDeclNGen_2709_;
v___y_2654_ = v_snapshotTasks_2714_;
v___y_2655_ = v___y_2701_;
v___y_2656_ = v_recordedDeps_2711_;
v___y_2657_ = v_infoState_2713_;
v___y_2658_ = v_ngen_2708_;
v___y_2659_ = v___y_2702_;
v___y_2660_ = v_messages_2712_;
v___y_2661_ = v___x_2716_;
goto v___jp_2650_;
}
else
{
lean_object* v_env_2717_; lean_object* v_nextMacroScope_2718_; lean_object* v_ngen_2719_; lean_object* v_auxDeclNGen_2720_; lean_object* v_traceState_2721_; lean_object* v_recordedDeps_2722_; lean_object* v_messages_2723_; lean_object* v_infoState_2724_; lean_object* v_snapshotTasks_2725_; lean_object* v_asyncMode_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v_env_2717_ = lean_ctor_get(v___x_2703_, 0);
lean_inc_ref(v_env_2717_);
v_nextMacroScope_2718_ = lean_ctor_get(v___x_2703_, 1);
lean_inc(v_nextMacroScope_2718_);
v_ngen_2719_ = lean_ctor_get(v___x_2703_, 2);
lean_inc_ref(v_ngen_2719_);
v_auxDeclNGen_2720_ = lean_ctor_get(v___x_2703_, 3);
lean_inc_ref(v_auxDeclNGen_2720_);
v_traceState_2721_ = lean_ctor_get(v___x_2703_, 4);
lean_inc_ref(v_traceState_2721_);
v_recordedDeps_2722_ = lean_ctor_get(v___x_2703_, 6);
lean_inc_ref(v_recordedDeps_2722_);
v_messages_2723_ = lean_ctor_get(v___x_2703_, 7);
lean_inc_ref(v_messages_2723_);
v_infoState_2724_ = lean_ctor_get(v___x_2703_, 8);
lean_inc_ref(v_infoState_2724_);
v_snapshotTasks_2725_ = lean_ctor_get(v___x_2703_, 9);
lean_inc_ref(v_snapshotTasks_2725_);
lean_dec(v___x_2703_);
v_asyncMode_2726_ = lean_ctor_get(v_toEnvExtension_2704_, 2);
lean_inc_ref_n(v_toEnvExtension_2704_, 2);
v___x_2727_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2704_, v_env_2717_);
lean_dec_ref(v_env_2717_);
v___x_2728_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2704_, v___x_2727_, v___f_2698_, v_asyncMode_2726_, v___x_2691_, v___x_2699_);
v___y_2651_ = v_nextMacroScope_2718_;
v___y_2652_ = v_traceState_2721_;
v___y_2653_ = v_auxDeclNGen_2720_;
v___y_2654_ = v_snapshotTasks_2725_;
v___y_2655_ = v___y_2701_;
v___y_2656_ = v_recordedDeps_2722_;
v___y_2657_ = v_infoState_2724_;
v___y_2658_ = v_ngen_2719_;
v___y_2659_ = v___y_2702_;
v___y_2660_ = v_messages_2723_;
v___y_2661_ = v___x_2728_;
goto v___jp_2650_;
}
}
}
else
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
lean_dec_ref_known(v_entry_2686_, 1);
lean_dec(v_hint_2642_);
lean_dec(v_mod_2640_);
v___x_2762_ = lean_box(0);
v___x_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2762_);
return v___x_2763_;
}
v___jp_2650_:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v_mctx_2666_; lean_object* v_zetaDeltaFVarIds_2667_; lean_object* v_postponed_2668_; lean_object* v_diag_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2680_; 
v___x_2662_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1);
v___x_2663_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2663_, 0, v___y_2661_);
lean_ctor_set(v___x_2663_, 1, v___y_2651_);
lean_ctor_set(v___x_2663_, 2, v___y_2658_);
lean_ctor_set(v___x_2663_, 3, v___y_2653_);
lean_ctor_set(v___x_2663_, 4, v___y_2652_);
lean_ctor_set(v___x_2663_, 5, v___x_2662_);
lean_ctor_set(v___x_2663_, 6, v___y_2656_);
lean_ctor_set(v___x_2663_, 7, v___y_2660_);
lean_ctor_set(v___x_2663_, 8, v___y_2657_);
lean_ctor_set(v___x_2663_, 9, v___y_2654_);
v___x_2664_ = lean_st_ref_put(v___y_2659_, v___x_2663_);
v___x_2665_ = lean_st_ref_take(v___y_2655_);
v_mctx_2666_ = lean_ctor_get(v___x_2665_, 0);
v_zetaDeltaFVarIds_2667_ = lean_ctor_get(v___x_2665_, 2);
v_postponed_2668_ = lean_ctor_get(v___x_2665_, 3);
v_diag_2669_ = lean_ctor_get(v___x_2665_, 4);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2680_ == 0)
{
lean_object* v_unused_2681_; 
v_unused_2681_ = lean_ctor_get(v___x_2665_, 1);
lean_dec(v_unused_2681_);
v___x_2671_ = v___x_2665_;
v_isShared_2672_ = v_isSharedCheck_2680_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_diag_2669_);
lean_inc(v_postponed_2668_);
lean_inc(v_zetaDeltaFVarIds_2667_);
lean_inc(v_mctx_2666_);
lean_dec(v___x_2665_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2680_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2676_; 
v___x_2673_ = lean_box(0);
v___x_2674_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 1, v___x_2674_);
v___x_2676_ = v___x_2671_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_mctx_2666_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v___x_2674_);
lean_ctor_set(v_reuseFailAlloc_2679_, 2, v_zetaDeltaFVarIds_2667_);
lean_ctor_set(v_reuseFailAlloc_2679_, 3, v_postponed_2668_);
lean_ctor_set(v_reuseFailAlloc_2679_, 4, v_diag_2669_);
v___x_2676_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2677_ = lean_st_ref_put(v___y_2655_, v___x_2676_);
v___x_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2673_);
return v___x_2678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___boxed(lean_object* v_mod_2764_, lean_object* v_isMeta_2765_, lean_object* v_hint_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
uint8_t v_isMeta_boxed_2774_; lean_object* v_res_2775_; 
v_isMeta_boxed_2774_ = lean_unbox(v_isMeta_2765_);
v_res_2775_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_mod_2764_, v_isMeta_boxed_2774_, v_hint_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(lean_object* v___x_2776_, lean_object* v_declName_2777_, lean_object* v_as_2778_, size_t v_sz_2779_, size_t v_i_2780_, lean_object* v_b_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
uint8_t v___x_2789_; 
v___x_2789_ = lean_usize_dec_lt(v_i_2780_, v_sz_2779_);
if (v___x_2789_ == 0)
{
lean_object* v___x_2790_; 
lean_dec(v_declName_2777_);
v___x_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2790_, 0, v_b_2781_);
return v___x_2790_;
}
else
{
lean_object* v___x_2791_; lean_object* v_modules_2792_; lean_object* v___x_2793_; lean_object* v_a_2794_; lean_object* v___x_2795_; lean_object* v_toImport_2796_; lean_object* v_module_2797_; lean_object* v___x_2798_; uint8_t v___x_2799_; lean_object* v___x_2800_; 
v___x_2791_ = l_Lean_Environment_header(v___x_2776_);
v_modules_2792_ = lean_ctor_get(v___x_2791_, 3);
lean_inc_ref(v_modules_2792_);
lean_dec_ref(v___x_2791_);
v___x_2793_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2794_ = lean_array_uget_borrowed(v_as_2778_, v_i_2780_);
v___x_2795_ = lean_array_get(v___x_2793_, v_modules_2792_, v_a_2794_);
lean_dec_ref(v_modules_2792_);
v_toImport_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc_ref(v_toImport_2796_);
lean_dec(v___x_2795_);
v_module_2797_ = lean_ctor_get(v_toImport_2796_, 0);
lean_inc(v_module_2797_);
lean_dec_ref(v_toImport_2796_);
v___x_2798_ = lean_box(0);
v___x_2799_ = 0;
lean_inc(v_declName_2777_);
v___x_2800_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_module_2797_, v___x_2799_, v_declName_2777_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
if (lean_obj_tag(v___x_2800_) == 0)
{
size_t v___x_2801_; size_t v___x_2802_; 
lean_dec_ref_known(v___x_2800_, 1);
v___x_2801_ = ((size_t)1ULL);
v___x_2802_ = lean_usize_add(v_i_2780_, v___x_2801_);
v_i_2780_ = v___x_2802_;
v_b_2781_ = v___x_2798_;
goto _start;
}
else
{
lean_dec(v_declName_2777_);
return v___x_2800_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5___boxed(lean_object* v___x_2804_, lean_object* v_declName_2805_, lean_object* v_as_2806_, lean_object* v_sz_2807_, lean_object* v_i_2808_, lean_object* v_b_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
size_t v_sz_boxed_2817_; size_t v_i_boxed_2818_; lean_object* v_res_2819_; 
v_sz_boxed_2817_ = lean_unbox_usize(v_sz_2807_);
lean_dec(v_sz_2807_);
v_i_boxed_2818_ = lean_unbox_usize(v_i_2808_);
lean_dec(v_i_2808_);
v_res_2819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(v___x_2804_, v_declName_2805_, v_as_2806_, v_sz_boxed_2817_, v_i_boxed_2818_, v_b_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec_ref(v_as_2806_);
lean_dec_ref(v___x_2804_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(lean_object* v_a_2820_, lean_object* v_x_2821_){
_start:
{
if (lean_obj_tag(v_x_2821_) == 0)
{
lean_object* v___x_2822_; 
v___x_2822_ = lean_box(0);
return v___x_2822_;
}
else
{
lean_object* v_key_2823_; lean_object* v_value_2824_; lean_object* v_tail_2825_; uint8_t v___x_2826_; 
v_key_2823_ = lean_ctor_get(v_x_2821_, 0);
v_value_2824_ = lean_ctor_get(v_x_2821_, 1);
v_tail_2825_ = lean_ctor_get(v_x_2821_, 2);
v___x_2826_ = lean_name_eq(v_key_2823_, v_a_2820_);
if (v___x_2826_ == 0)
{
v_x_2821_ = v_tail_2825_;
goto _start;
}
else
{
lean_object* v___x_2828_; 
lean_inc(v_value_2824_);
v___x_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2828_, 0, v_value_2824_);
return v___x_2828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_a_2829_, lean_object* v_x_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(v_a_2829_, v_x_2830_);
lean_dec(v_x_2830_);
lean_dec(v_a_2829_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(lean_object* v_m_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v_buckets_2834_; lean_object* v___x_2835_; uint64_t v___y_2837_; 
v_buckets_2834_ = lean_ctor_get(v_m_2832_, 1);
v___x_2835_ = lean_array_get_size(v_buckets_2834_);
if (lean_obj_tag(v_a_2833_) == 0)
{
uint64_t v___x_2851_; 
v___x_2851_ = 1723ULL;
v___y_2837_ = v___x_2851_;
goto v___jp_2836_;
}
else
{
uint64_t v_hash_2852_; 
v_hash_2852_ = lean_ctor_get_uint64(v_a_2833_, sizeof(void*)*2);
v___y_2837_ = v_hash_2852_;
goto v___jp_2836_;
}
v___jp_2836_:
{
uint64_t v___x_2838_; uint64_t v___x_2839_; uint64_t v_fold_2840_; uint64_t v___x_2841_; uint64_t v___x_2842_; uint64_t v___x_2843_; size_t v___x_2844_; size_t v___x_2845_; size_t v___x_2846_; size_t v___x_2847_; size_t v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2838_ = 32ULL;
v___x_2839_ = lean_uint64_shift_right(v___y_2837_, v___x_2838_);
v_fold_2840_ = lean_uint64_xor(v___y_2837_, v___x_2839_);
v___x_2841_ = 16ULL;
v___x_2842_ = lean_uint64_shift_right(v_fold_2840_, v___x_2841_);
v___x_2843_ = lean_uint64_xor(v_fold_2840_, v___x_2842_);
v___x_2844_ = lean_uint64_to_usize(v___x_2843_);
v___x_2845_ = lean_usize_of_nat(v___x_2835_);
v___x_2846_ = ((size_t)1ULL);
v___x_2847_ = lean_usize_sub(v___x_2845_, v___x_2846_);
v___x_2848_ = lean_usize_land(v___x_2844_, v___x_2847_);
v___x_2849_ = lean_array_uget_borrowed(v_buckets_2834_, v___x_2848_);
v___x_2850_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(v_a_2833_, v___x_2849_);
return v___x_2850_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_m_2853_, lean_object* v_a_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(v_m_2853_, v_a_2854_);
lean_dec(v_a_2854_);
lean_dec_ref(v_m_2853_);
return v_res_2855_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(lean_object* v_declName_2859_, uint8_t v_isMeta_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v_env_2873_; lean_object* v___y_2875_; lean_object* v___x_2888_; 
v___x_2868_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0);
v___x_2869_ = lean_st_ref_get(v___y_2866_);
v_env_2873_ = lean_ctor_get(v___x_2869_, 0);
lean_inc_ref(v_env_2873_);
lean_dec(v___x_2869_);
v___x_2888_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2873_, v_declName_2859_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_dec_ref(v_env_2873_);
lean_dec(v_declName_2859_);
goto v___jp_2870_;
}
else
{
lean_object* v_val_2889_; lean_object* v___x_2890_; lean_object* v_modules_2891_; lean_object* v___x_2892_; uint8_t v___x_2893_; 
v_val_2889_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_val_2889_);
lean_dec_ref_known(v___x_2888_, 1);
v___x_2890_ = l_Lean_Environment_header(v_env_2873_);
v_modules_2891_ = lean_ctor_get(v___x_2890_, 3);
lean_inc_ref(v_modules_2891_);
lean_dec_ref(v___x_2890_);
v___x_2892_ = lean_array_get_size(v_modules_2891_);
v___x_2893_ = lean_nat_dec_lt(v_val_2889_, v___x_2892_);
if (v___x_2893_ == 0)
{
lean_dec_ref(v_modules_2891_);
lean_dec(v_val_2889_);
lean_dec_ref(v_env_2873_);
lean_dec(v_declName_2859_);
goto v___jp_2870_;
}
else
{
lean_object* v___x_2894_; lean_object* v___x_2895_; uint8_t v___y_2897_; 
v___x_2894_ = lean_array_fget(v_modules_2891_, v_val_2889_);
lean_dec(v_val_2889_);
lean_dec_ref(v_modules_2891_);
v___x_2895_ = lean_st_ref_get(v___y_2866_);
if (v_isMeta_2860_ == 0)
{
lean_dec(v___x_2895_);
v___y_2897_ = v_isMeta_2860_;
goto v___jp_2896_;
}
else
{
lean_object* v_env_2908_; uint8_t v___x_2909_; 
v_env_2908_ = lean_ctor_get(v___x_2895_, 0);
lean_inc_ref(v_env_2908_);
lean_dec(v___x_2895_);
lean_inc(v_declName_2859_);
v___x_2909_ = l_Lean_isMarkedMeta(v_env_2908_, v_declName_2859_);
if (v___x_2909_ == 0)
{
v___y_2897_ = v_isMeta_2860_;
goto v___jp_2896_;
}
else
{
uint8_t v___x_2910_; 
v___x_2910_ = 0;
v___y_2897_ = v___x_2910_;
goto v___jp_2896_;
}
}
v___jp_2896_:
{
lean_object* v_toImport_2898_; lean_object* v_module_2899_; lean_object* v___x_2900_; 
v_toImport_2898_ = lean_ctor_get(v___x_2894_, 0);
lean_inc_ref(v_toImport_2898_);
lean_dec(v___x_2894_);
v_module_2899_ = lean_ctor_get(v_toImport_2898_, 0);
lean_inc(v_module_2899_);
lean_dec_ref(v_toImport_2898_);
lean_inc(v_declName_2859_);
v___x_2900_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_module_2899_, v___y_2897_, v_declName_2859_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
lean_dec_ref_known(v___x_2900_, 1);
v___x_2901_ = l_Lean_indirectModUseExt;
v___x_2902_ = lean_box(1);
v___x_2903_ = lean_box(0);
lean_inc_ref(v_env_2873_);
v___x_2904_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2868_, v___x_2901_, v_env_2873_, v___x_2902_, v___x_2903_);
v___x_2905_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(v___x_2904_, v_declName_2859_);
lean_dec(v___x_2904_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v___x_2906_; 
v___x_2906_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__1));
v___y_2875_ = v___x_2906_;
goto v___jp_2874_;
}
else
{
lean_object* v_val_2907_; 
v_val_2907_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_val_2907_);
lean_dec_ref_known(v___x_2905_, 1);
v___y_2875_ = v_val_2907_;
goto v___jp_2874_;
}
}
else
{
lean_dec_ref(v_env_2873_);
lean_dec(v_declName_2859_);
return v___x_2900_;
}
}
}
}
v___jp_2870_:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2871_ = lean_box(0);
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
return v___x_2872_;
}
v___jp_2874_:
{
lean_object* v___x_2876_; size_t v_sz_2877_; size_t v___x_2878_; lean_object* v___x_2879_; 
v___x_2876_ = lean_box(0);
v_sz_2877_ = lean_array_size(v___y_2875_);
v___x_2878_ = ((size_t)0ULL);
v___x_2879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(v_env_2873_, v_declName_2859_, v___y_2875_, v_sz_2877_, v___x_2878_, v___x_2876_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
lean_dec_ref(v___y_2875_);
lean_dec_ref(v_env_2873_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2886_ == 0)
{
lean_object* v_unused_2887_; 
v_unused_2887_ = lean_ctor_get(v___x_2879_, 0);
lean_dec(v_unused_2887_);
v___x_2881_ = v___x_2879_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_dec(v___x_2879_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v___x_2876_);
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2876_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
else
{
return v___x_2879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___boxed(lean_object* v_declName_2911_, lean_object* v_isMeta_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
uint8_t v_isMeta_boxed_2920_; lean_object* v_res_2921_; 
v_isMeta_boxed_2920_ = lean_unbox(v_isMeta_2912_);
v_res_2921_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(v_declName_2911_, v_isMeta_boxed_2920_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(lean_object* v_as_x27_2922_, lean_object* v_b_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
if (lean_obj_tag(v_as_x27_2922_) == 0)
{
lean_object* v___x_2931_; 
v___x_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2931_, 0, v_b_2923_);
return v___x_2931_;
}
else
{
lean_object* v_head_2932_; lean_object* v_tail_2933_; lean_object* v___x_2934_; uint8_t v___x_2935_; lean_object* v___x_2936_; 
v_head_2932_ = lean_ctor_get(v_as_x27_2922_, 0);
v_tail_2933_ = lean_ctor_get(v_as_x27_2922_, 1);
v___x_2934_ = lean_box(0);
v___x_2935_ = 1;
lean_inc(v_head_2932_);
v___x_2936_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(v_head_2932_, v___x_2935_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_dec_ref_known(v___x_2936_, 1);
v_as_x27_2922_ = v_tail_2933_;
v_b_2923_ = v___x_2934_;
goto _start;
}
else
{
return v___x_2936_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2938_, lean_object* v_b_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_as_x27_2938_, v_b_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v_as_x27_2938_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4(lean_object* v_env_2948_, lean_object* v_currNamespace_2949_, lean_object* v_openDecls_2950_, lean_object* v_n_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2954_ = l_Lean_ResolveName_resolveNamespace(v_env_2948_, v_currNamespace_2949_, v_openDecls_2950_, v_n_2951_);
v___x_2955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
lean_ctor_set(v___x_2955_, 1, v___y_2953_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4___boxed(lean_object* v_env_2956_, lean_object* v_currNamespace_2957_, lean_object* v_openDecls_2958_, lean_object* v_n_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4(v_env_2956_, v_currNamespace_2957_, v_openDecls_2958_, v_n_2959_, v___y_2960_, v___y_2961_);
lean_dec_ref(v___y_2960_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2(lean_object* v_currNamespace_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2966_, 0, v_currNamespace_2963_);
lean_ctor_set(v___x_2966_, 1, v___y_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2___boxed(lean_object* v_currNamespace_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2(v_currNamespace_2967_, v___y_2968_, v___y_2969_);
lean_dec_ref(v___y_2968_);
return v_res_2970_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2971_ = lean_box(0);
v___x_2972_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
lean_ctor_set(v___x_2973_, 1, v___x_2971_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg(){
_start:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2975_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0);
v___x_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___boxed(lean_object* v___y_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
return v_res_2978_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = l_Lean_maxRecDepthErrorMessage;
v___x_2985_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2984_);
return v___x_2985_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3);
v___x_2987_ = l_Lean_MessageData_ofFormat(v___x_2986_);
return v___x_2987_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2988_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4);
v___x_2989_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__2));
v___x_2990_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
lean_ctor_set(v___x_2990_, 1, v___x_2988_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(lean_object* v_ref_2991_){
_start:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2993_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5);
v___x_2994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2994_, 0, v_ref_2991_);
lean_ctor_set(v___x_2994_, 1, v___x_2993_);
v___x_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_ref_2996_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(lean_object* v_x_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v___x_3008_; lean_object* v_toCold_3009_; lean_object* v_env_3010_; lean_object* v_currRecDepth_3011_; lean_object* v_ref_3012_; lean_object* v_maxRecDepth_3013_; lean_object* v_currNamespace_3014_; lean_object* v_openDecls_3015_; lean_object* v_quotContext_3016_; lean_object* v_currMacroScope_3017_; lean_object* v___f_3018_; lean_object* v___f_3019_; lean_object* v___x_3020_; lean_object* v___f_3021_; lean_object* v___f_3022_; lean_object* v___f_3023_; lean_object* v_methods_3024_; lean_object* v___x_3025_; lean_object* v_nextMacroScope_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3008_ = lean_st_ref_get(v___y_3006_);
v_toCold_3009_ = lean_ctor_get(v___y_3005_, 0);
v_env_3010_ = lean_ctor_get(v___x_3008_, 0);
lean_inc_ref_n(v_env_3010_, 4);
lean_dec(v___x_3008_);
v_currRecDepth_3011_ = lean_ctor_get(v___y_3005_, 1);
v_ref_3012_ = lean_ctor_get(v___y_3005_, 2);
v_maxRecDepth_3013_ = lean_ctor_get(v_toCold_3009_, 3);
v_currNamespace_3014_ = lean_ctor_get(v_toCold_3009_, 4);
v_openDecls_3015_ = lean_ctor_get(v_toCold_3009_, 5);
v_quotContext_3016_ = lean_ctor_get(v_toCold_3009_, 8);
v_currMacroScope_3017_ = lean_ctor_get(v_toCold_3009_, 9);
v___f_3018_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3018_, 0, v_env_3010_);
v___f_3019_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_3019_, 0, v_env_3010_);
v___x_3020_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3005_);
lean_inc_n(v_currNamespace_3014_, 3);
v___f_3021_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3021_, 0, v_currNamespace_3014_);
lean_inc_n(v_openDecls_3015_, 2);
v___f_3022_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_3022_, 0, v_env_3010_);
lean_closure_set(v___f_3022_, 1, v___x_3020_);
lean_closure_set(v___f_3022_, 2, v_currNamespace_3014_);
lean_closure_set(v___f_3022_, 3, v_openDecls_3015_);
v___f_3023_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_3023_, 0, v_env_3010_);
lean_closure_set(v___f_3023_, 1, v_currNamespace_3014_);
lean_closure_set(v___f_3023_, 2, v_openDecls_3015_);
v_methods_3024_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_3024_, 0, v___f_3019_);
lean_ctor_set(v_methods_3024_, 1, v___f_3021_);
lean_ctor_set(v_methods_3024_, 2, v___f_3018_);
lean_ctor_set(v_methods_3024_, 3, v___f_3023_);
lean_ctor_set(v_methods_3024_, 4, v___f_3022_);
v___x_3025_ = lean_st_ref_get(v___y_3006_);
v_nextMacroScope_3026_ = lean_ctor_get(v___x_3025_, 1);
lean_inc(v_nextMacroScope_3026_);
lean_dec(v___x_3025_);
lean_inc(v_ref_3012_);
lean_inc(v_maxRecDepth_3013_);
lean_inc(v_currRecDepth_3011_);
lean_inc(v_currMacroScope_3017_);
lean_inc(v_quotContext_3016_);
v___x_3027_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3027_, 0, v_methods_3024_);
lean_ctor_set(v___x_3027_, 1, v_quotContext_3016_);
lean_ctor_set(v___x_3027_, 2, v_currMacroScope_3017_);
lean_ctor_set(v___x_3027_, 3, v_currRecDepth_3011_);
lean_ctor_set(v___x_3027_, 4, v_maxRecDepth_3013_);
lean_ctor_set(v___x_3027_, 5, v_ref_3012_);
v___x_3028_ = lean_box(0);
v___x_3029_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3029_, 0, v_nextMacroScope_3026_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
lean_ctor_set(v___x_3029_, 2, v___x_3028_);
v___x_3030_ = lean_apply_2(v_x_3000_, v___x_3027_, v___x_3029_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v_a_3032_; lean_object* v_macroScope_3033_; lean_object* v_traceMsgs_3034_; lean_object* v_expandedMacroDecls_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 1);
lean_inc(v_a_3031_);
v_a_3032_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3032_);
lean_dec_ref_known(v___x_3030_, 2);
v_macroScope_3033_ = lean_ctor_get(v_a_3031_, 0);
lean_inc(v_macroScope_3033_);
v_traceMsgs_3034_ = lean_ctor_get(v_a_3031_, 1);
lean_inc(v_traceMsgs_3034_);
v_expandedMacroDecls_3035_ = lean_ctor_get(v_a_3031_, 2);
lean_inc(v_expandedMacroDecls_3035_);
lean_dec(v_a_3031_);
v___x_3036_ = lean_box(0);
v___x_3037_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_expandedMacroDecls_3035_, v___x_3036_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
lean_dec(v_expandedMacroDecls_3035_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v___x_3038_; lean_object* v_env_3039_; lean_object* v_ngen_3040_; lean_object* v_auxDeclNGen_3041_; lean_object* v_traceState_3042_; lean_object* v_cache_3043_; lean_object* v_recordedDeps_3044_; lean_object* v_messages_3045_; lean_object* v_infoState_3046_; lean_object* v_snapshotTasks_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3073_; 
lean_dec_ref_known(v___x_3037_, 1);
v___x_3038_ = lean_st_ref_take(v___y_3006_);
v_env_3039_ = lean_ctor_get(v___x_3038_, 0);
v_ngen_3040_ = lean_ctor_get(v___x_3038_, 2);
v_auxDeclNGen_3041_ = lean_ctor_get(v___x_3038_, 3);
v_traceState_3042_ = lean_ctor_get(v___x_3038_, 4);
v_cache_3043_ = lean_ctor_get(v___x_3038_, 5);
v_recordedDeps_3044_ = lean_ctor_get(v___x_3038_, 6);
v_messages_3045_ = lean_ctor_get(v___x_3038_, 7);
v_infoState_3046_ = lean_ctor_get(v___x_3038_, 8);
v_snapshotTasks_3047_ = lean_ctor_get(v___x_3038_, 9);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3073_ == 0)
{
lean_object* v_unused_3074_; 
v_unused_3074_ = lean_ctor_get(v___x_3038_, 1);
lean_dec(v_unused_3074_);
v___x_3049_ = v___x_3038_;
v_isShared_3050_ = v_isSharedCheck_3073_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_snapshotTasks_3047_);
lean_inc(v_infoState_3046_);
lean_inc(v_messages_3045_);
lean_inc(v_recordedDeps_3044_);
lean_inc(v_cache_3043_);
lean_inc(v_traceState_3042_);
lean_inc(v_auxDeclNGen_3041_);
lean_inc(v_ngen_3040_);
lean_inc(v_env_3039_);
lean_dec(v___x_3038_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3073_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 1, v_macroScope_3033_);
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_env_3039_);
lean_ctor_set(v_reuseFailAlloc_3072_, 1, v_macroScope_3033_);
lean_ctor_set(v_reuseFailAlloc_3072_, 2, v_ngen_3040_);
lean_ctor_set(v_reuseFailAlloc_3072_, 3, v_auxDeclNGen_3041_);
lean_ctor_set(v_reuseFailAlloc_3072_, 4, v_traceState_3042_);
lean_ctor_set(v_reuseFailAlloc_3072_, 5, v_cache_3043_);
lean_ctor_set(v_reuseFailAlloc_3072_, 6, v_recordedDeps_3044_);
lean_ctor_set(v_reuseFailAlloc_3072_, 7, v_messages_3045_);
lean_ctor_set(v_reuseFailAlloc_3072_, 8, v_infoState_3046_);
lean_ctor_set(v_reuseFailAlloc_3072_, 9, v_snapshotTasks_3047_);
v___x_3052_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3053_ = lean_st_ref_put(v___y_3006_, v___x_3052_);
v___x_3054_ = l_List_reverse___redArg(v_traceMsgs_3034_);
v___x_3055_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(v___x_3054_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3062_ == 0)
{
lean_object* v_unused_3063_; 
v_unused_3063_ = lean_ctor_get(v___x_3055_, 0);
lean_dec(v_unused_3063_);
v___x_3057_ = v___x_3055_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_dec(v___x_3055_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 0, v_a_3032_);
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3032_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec(v_a_3032_);
v_a_3064_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3055_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3055_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
}
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec(v_traceMsgs_3034_);
lean_dec(v_macroScope_3033_);
lean_dec(v_a_3032_);
v_a_3075_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_3037_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3037_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
else
{
lean_object* v_a_3083_; 
v_a_3083_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3083_);
lean_dec_ref_known(v___x_3030_, 2);
if (lean_obj_tag(v_a_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v_a_3085_; lean_object* v___x_3086_; uint8_t v___x_3087_; 
v_a_3084_ = lean_ctor_get(v_a_3083_, 0);
lean_inc(v_a_3084_);
v_a_3085_ = lean_ctor_get(v_a_3083_, 1);
lean_inc_ref(v_a_3085_);
lean_dec_ref_known(v_a_3083_, 2);
v___x_3086_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___closed__0));
v___x_3087_ = lean_string_dec_eq(v_a_3085_, v___x_3086_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3088_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3088_, 0, v_a_3085_);
v___x_3089_ = l_Lean_MessageData_ofFormat(v___x_3088_);
v___x_3090_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_a_3084_, v___x_3089_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
lean_dec(v_a_3084_);
return v___x_3090_;
}
else
{
lean_object* v___x_3091_; 
lean_dec_ref(v_a_3085_);
v___x_3091_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_a_3084_);
return v___x_3091_;
}
}
else
{
lean_object* v___x_3092_; 
v___x_3092_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
return v___x_3092_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___boxed(lean_object* v_x_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v_x_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(lean_object* v_pre_3102_, lean_object* v_binders_3103_, lean_object* v_type_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_){
_start:
{
lean_object* v_a_3113_; lean_object* v___f_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
lean_inc_ref(v_pre_3102_);
v___f_3116_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1___boxed), 10, 2);
lean_closure_set(v___f_3116_, 0, v_type_3104_);
lean_closure_set(v___f_3116_, 1, v_pre_3102_);
v___x_3117_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___boxed), 10, 3);
lean_closure_set(v___x_3117_, 0, lean_box(0));
lean_closure_set(v___x_3117_, 1, v_binders_3103_);
lean_closure_set(v___x_3117_, 2, v___f_3116_);
v___x_3118_ = l_Lean_Elab_Term_withAutoBoundImplicit___redArg(v___x_3117_, v_a_3105_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3109_, v_a_3110_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_a_3119_; 
lean_dec_ref(v_pre_3102_);
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_a_3119_);
lean_dec_ref_known(v___x_3118_, 1);
v_a_3113_ = v_a_3119_;
goto v___jp_3112_;
}
else
{
lean_object* v_a_3120_; uint8_t v___x_3121_; 
v_a_3120_ = lean_ctor_get(v___x_3118_, 0);
v___x_3121_ = l_Lean_Exception_isInterrupt(v_a_3120_);
if (v___x_3121_ == 0)
{
uint8_t v___x_3122_; 
lean_inc(v_a_3120_);
v___x_3122_ = l_Lean_Exception_isRuntime(v_a_3120_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
lean_dec_ref_known(v___x_3118_, 1);
v___x_3123_ = lean_box(0);
v___x_3124_ = l_Lean_Name_str___override(v___x_3123_, v_pre_3102_);
v___x_3125_ = l_Lean_Core_mkFreshUserName(v___x_3124_, v_a_3109_, v_a_3110_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_object* v_a_3126_; 
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_a_3126_);
lean_dec_ref_known(v___x_3125_, 1);
v_a_3113_ = v_a_3126_;
goto v___jp_3112_;
}
else
{
return v___x_3125_;
}
}
else
{
lean_dec_ref(v_pre_3102_);
return v___x_3118_;
}
}
else
{
lean_dec_ref(v_pre_3102_);
return v___x_3118_;
}
}
v___jp_3112_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3114_ = lean_alloc_closure((void*)(l_Lean_Elab_mkUnusedBaseName___boxed), 3, 1);
lean_closure_set(v___x_3114_, 0, v_a_3113_);
v___x_3115_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v___x_3114_, v_a_3105_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3109_, v_a_3110_);
return v___x_3115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___boxed(lean_object* v_pre_3127_, lean_object* v_binders_3128_, lean_object* v_type_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(v_pre_3127_, v_binders_3128_, v_type_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
lean_dec(v_a_3135_);
lean_dec_ref(v_a_3134_);
lean_dec(v_a_3133_);
lean_dec_ref(v_a_3132_);
lean_dec(v_a_3131_);
lean_dec_ref(v_a_3130_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2(lean_object* v_00_u03b1_3138_, lean_object* v_x_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v___x_3142_; 
v___x_3142_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v_x_3139_, v___y_3141_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3143_, lean_object* v_x_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v_res_3147_; 
v_res_3147_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2(v_00_u03b1_3143_, v_x_3144_, v___y_3145_, v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec_ref(v_x_3144_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7(lean_object* v_00_u03b1_3148_, lean_object* v_ref_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v___x_3157_; 
v___x_3157_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_ref_3149_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___boxed(lean_object* v_00_u03b1_3158_, lean_object* v_ref_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7(v_00_u03b1_3158_, v_ref_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8(lean_object* v_00_u03b1_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v___x_3176_; 
v___x_3176_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___boxed(lean_object* v_00_u03b1_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8(v_00_u03b1_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1(lean_object* v_00_u03b1_3186_, lean_object* v_x_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v_x_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___boxed(lean_object* v_00_u03b1_3196_, lean_object* v_x_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1(v_00_u03b1_3196_, v_x_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1(lean_object* v_cls_3206_, lean_object* v_msg_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
lean_object* v___x_3215_; 
v___x_3215_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_3206_, v_msg_3207_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___boxed(lean_object* v_cls_3216_, lean_object* v_msg_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1(v_cls_3216_, v_msg_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4(lean_object* v_as_3226_, lean_object* v_as_x27_3227_, lean_object* v_b_3228_, lean_object* v_a_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_as_x27_3227_, v_b_3228_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___boxed(lean_object* v_as_3238_, lean_object* v_as_x27_3239_, lean_object* v_b_3240_, lean_object* v_a_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4(v_as_3238_, v_as_x27_3239_, v_b_3240_, v_a_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v_as_x27_3239_);
lean_dec(v_as_3238_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6(lean_object* v_00_u03b1_3250_, lean_object* v_ref_3251_, lean_object* v_msg_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_ref_3251_, v_msg_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3261_, lean_object* v_ref_3262_, lean_object* v_msg_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6(v_00_u03b1_3261_, v_ref_3262_, v_msg_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v_ref_3262_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_3272_, lean_object* v_m_3273_, lean_object* v_a_3274_){
_start:
{
lean_object* v___x_3275_; 
v___x_3275_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(v_m_3273_, v_a_3274_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3276_, lean_object* v_m_3277_, lean_object* v_a_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6(v_00_u03b2_3276_, v_m_3277_, v_a_3278_);
lean_dec(v_a_3278_);
lean_dec_ref(v_m_3277_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10(lean_object* v_00_u03b1_3280_, lean_object* v_msg_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___boxed(lean_object* v_00_u03b1_3290_, lean_object* v_msg_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10(v_00_u03b1_3290_, v_msg_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
return v_res_3299_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_3300_, lean_object* v_x_3301_, lean_object* v_x_3302_){
_start:
{
uint8_t v___x_3303_; 
v___x_3303_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v_x_3301_, v_x_3302_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3304_, lean_object* v_x_3305_, lean_object* v_x_3306_){
_start:
{
uint8_t v_res_3307_; lean_object* v_r_3308_; 
v_res_3307_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7(v_00_u03b2_3304_, v_x_3305_, v_x_3306_);
lean_dec_ref(v_x_3306_);
lean_dec_ref(v_x_3305_);
v_r_3308_ = lean_box(v_res_3307_);
return v_r_3308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_3309_, lean_object* v_a_3310_, lean_object* v_x_3311_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(v_a_3310_, v_x_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_3313_, lean_object* v_a_3314_, lean_object* v_x_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_3313_, v_a_3314_, v_x_3315_);
lean_dec(v_x_3315_);
lean_dec(v_a_3314_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15(lean_object* v_msgData_3317_, lean_object* v_macroStack_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v___x_3326_; 
v___x_3326_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_msgData_3317_, v_macroStack_3318_, v___y_3323_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___boxed(lean_object* v_msgData_3327_, lean_object* v_macroStack_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15(v_msgData_3327_, v_macroStack_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
return v_res_3336_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_3337_, lean_object* v_x_3338_, size_t v_x_3339_, lean_object* v_x_3340_){
_start:
{
uint8_t v___x_3341_; 
v___x_3341_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_3338_, v_x_3339_, v_x_3340_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3342_, lean_object* v_x_3343_, lean_object* v_x_3344_, lean_object* v_x_3345_){
_start:
{
size_t v_x_15960__boxed_3346_; uint8_t v_res_3347_; lean_object* v_r_3348_; 
v_x_15960__boxed_3346_ = lean_unbox_usize(v_x_3344_);
lean_dec(v_x_3344_);
v_res_3347_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11(v_00_u03b2_3342_, v_x_3343_, v_x_15960__boxed_3346_, v_x_3345_);
lean_dec_ref(v_x_3345_);
lean_dec_ref(v_x_3343_);
v_r_3348_ = lean_box(v_res_3347_);
return v_r_3348_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15(lean_object* v_00_u03b2_3349_, lean_object* v_keys_3350_, lean_object* v_vals_3351_, lean_object* v_heq_3352_, lean_object* v_i_3353_, lean_object* v_k_3354_){
_start:
{
uint8_t v___x_3355_; 
v___x_3355_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_keys_3350_, v_i_3353_, v_k_3354_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___boxed(lean_object* v_00_u03b2_3356_, lean_object* v_keys_3357_, lean_object* v_vals_3358_, lean_object* v_heq_3359_, lean_object* v_i_3360_, lean_object* v_k_3361_){
_start:
{
uint8_t v_res_3362_; lean_object* v_r_3363_; 
v_res_3362_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15(v_00_u03b2_3356_, v_keys_3357_, v_vals_3358_, v_heq_3359_, v_i_3360_, v_k_3361_);
lean_dec_ref(v_k_3361_);
lean_dec_ref(v_vals_3358_);
lean_dec_ref(v_keys_3357_);
v_r_3363_ = lean_box(v_res_3362_);
return v_r_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__0(lean_object* v_binders_3365_, lean_object* v_type_3366_, lean_object* v_x_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = ((lean_object*)(l_Lean_Elab_Command_mkInstanceName___lam__0___closed__0));
v___x_3376_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(v___x_3375_, v_binders_3365_, v_type_3366_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__0___boxed(lean_object* v_binders_3377_, lean_object* v_type_3378_, lean_object* v_x_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Lean_Elab_Command_mkInstanceName___lam__0(v_binders_3377_, v_type_3378_, v_x_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec_ref(v_x_3379_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__1(lean_object* v_a_3388_, lean_object* v_val_3389_, lean_object* v_a_x3f_3390_){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3392_ = lean_box(0);
v___x_3393_ = lean_st_ref_swap(v_a_3388_, v_val_3389_);
lean_dec(v___x_3393_);
v___x_3394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3392_);
return v___x_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__1___boxed(lean_object* v_a_3395_, lean_object* v_val_3396_, lean_object* v_a_x3f_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l_Lean_Elab_Command_mkInstanceName___lam__1(v_a_3395_, v_val_3396_, v_a_x3f_3397_);
lean_dec(v_a_x3f_3397_);
lean_dec(v_a_3395_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName(lean_object* v_binders_3400_, lean_object* v_type_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_){
_start:
{
lean_object* v___f_3405_; lean_object* v___x_3406_; lean_object* v_r_3407_; 
v___f_3405_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkInstanceName___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3405_, 0, v_binders_3400_);
lean_closure_set(v___f_3405_, 1, v_type_3401_);
v___x_3406_ = lean_st_ref_get(v_a_3403_);
v_r_3407_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_3405_, v_a_3402_, v_a_3403_);
if (lean_obj_tag(v_r_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3424_; 
v_a_3408_ = lean_ctor_get(v_r_3407_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v_r_3407_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3410_ = v_r_3407_;
v_isShared_3411_ = v_isSharedCheck_3424_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v_r_3407_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3424_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
lean_inc(v_a_3408_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set_tag(v___x_3410_, 1);
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
lean_object* v___x_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
v___x_3414_ = l_Lean_Elab_Command_mkInstanceName___lam__1(v_a_3403_, v___x_3406_, v___x_3413_);
lean_dec_ref(v___x_3413_);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3421_ == 0)
{
lean_object* v_unused_3422_; 
v_unused_3422_ = lean_ctor_get(v___x_3414_, 0);
lean_dec(v_unused_3422_);
v___x_3416_ = v___x_3414_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_dec(v___x_3414_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v_a_3408_);
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3408_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
v_a_3425_ = lean_ctor_get(v_r_3407_, 0);
lean_inc(v_a_3425_);
lean_dec_ref_known(v_r_3407_, 1);
v___x_3426_ = lean_box(0);
v___x_3427_ = l_Lean_Elab_Command_mkInstanceName___lam__1(v_a_3403_, v___x_3406_, v___x_3426_);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3434_ == 0)
{
lean_object* v_unused_3435_; 
v_unused_3435_ = lean_ctor_get(v___x_3427_, 0);
lean_dec(v_unused_3435_);
v___x_3429_ = v___x_3427_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_dec(v___x_3427_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set_tag(v___x_3429_, 1);
lean_ctor_set(v___x_3429_, 0, v_a_3425_);
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3425_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___boxed(lean_object* v_binders_3436_, lean_object* v_type_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l_Lean_Elab_Command_mkInstanceName(v_binders_3436_, v_type_3437_, v_a_3438_, v_a_3439_);
lean_dec(v_a_3439_);
lean_dec_ref(v_a_3438_);
return v_res_3441_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DeclNameGen(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_DeclNameGen(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DeclNameGen(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DeclNameGen(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_DeclNameGen(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_DeclNameGen(builtin);
}
#ifdef __cplusplus
}
#endif
