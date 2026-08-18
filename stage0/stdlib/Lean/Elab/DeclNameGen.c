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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
uint8_t l_Lean_Expr_isSort(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkUnusedBaseName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0;
static lean_once_cell_t l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1;
static lean_once_cell_t l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0 = (const lean_object*)&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0_value;
static const lean_string_object l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Forall"};
static const lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__1 = (const lean_object*)&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__1_value;
static const lean_string_object l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prop"};
static const lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__2 = (const lean_object*)&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__2_value;
static const lean_string_object l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Type"};
static const lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__3 = (const lean_object*)&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__3_value;
static const lean_string_object l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Sort"};
static const lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__4 = (const lean_object*)&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0;
static lean_once_cell_t l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1;
static lean_once_cell_t l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__2;
static const lean_closure_object l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__3 = (const lean_object*)&l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__3_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___boxed(lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__22_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_str_12_; lean_object* v___x_13_; lean_object* v_env_18_; lean_object* v___x_19_; 
v_str_12_ = lean_ctor_get(v_declName_11_, 1);
lean_inc_ref(v_str_12_);
v___x_13_ = lean_st_ref_get(v_a_2_);
v_env_18_ = lean_ctor_get(v___x_13_, 0);
lean_inc_ref_n(v_env_18_, 2);
lean_dec(v___x_13_);
v___x_19_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_18_, v_declName_11_);
if (lean_obj_tag(v___x_19_) == 1)
{
lean_object* v_val_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_50_; 
v_val_20_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_50_ == 0)
{
v___x_22_ = v___x_19_;
v_isShared_23_ = v_isSharedCheck_50_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_val_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_50_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v_ctorName_24_; lean_object* v_numParams_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; uint8_t v___x_29_; 
v_ctorName_24_ = lean_ctor_get(v_val_20_, 0);
lean_inc(v_ctorName_24_);
v_numParams_25_ = lean_ctor_get(v_val_20_, 1);
lean_inc(v_numParams_25_);
lean_dec(v_val_20_);
v___x_26_ = l_Lean_Expr_getAppNumArgs(v_e_1_);
v___x_27_ = lean_unsigned_to_nat(1u);
v___x_28_ = lean_nat_add(v_numParams_25_, v___x_27_);
lean_dec(v_numParams_25_);
v___x_29_ = lean_nat_dec_eq(v___x_26_, v___x_28_);
lean_dec(v___x_28_);
lean_dec(v___x_26_);
if (v___x_29_ == 0)
{
lean_object* v___x_30_; lean_object* v___x_32_; 
lean_dec(v_ctorName_24_);
lean_dec_ref(v_env_18_);
lean_dec_ref(v_str_12_);
v___x_30_ = lean_box(0);
if (v_isShared_23_ == 0)
{
lean_ctor_set_tag(v___x_22_, 0);
lean_ctor_set(v___x_22_, 0, v___x_30_);
v___x_32_ = v___x_22_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___x_30_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
else
{
uint8_t v___x_34_; lean_object* v___x_35_; 
lean_del_object(v___x_22_);
v___x_34_ = 0;
lean_inc_ref(v_env_18_);
v___x_35_ = l_Lean_Environment_find_x3f(v_env_18_, v_ctorName_24_, v___x_34_);
if (lean_obj_tag(v___x_35_) == 1)
{
lean_object* v_val_36_; 
v_val_36_ = lean_ctor_get(v___x_35_, 0);
lean_inc(v_val_36_);
lean_dec_ref_known(v___x_35_, 1);
if (lean_obj_tag(v_val_36_) == 6)
{
lean_object* v_val_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_49_; 
v_val_37_ = lean_ctor_get(v_val_36_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v_val_36_);
if (v_isSharedCheck_49_ == 0)
{
v___x_39_ = v_val_36_;
v_isShared_40_ = v_isSharedCheck_49_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_val_37_);
lean_dec(v_val_36_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_49_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v_induct_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v_induct_41_ = lean_ctor_get(v_val_37_, 1);
lean_inc(v_induct_41_);
lean_dec_ref(v_val_37_);
v___x_42_ = lean_box(0);
v___x_43_ = l_Lean_Name_str___override(v___x_42_, v_str_12_);
v___x_44_ = l_Lean_isSubobjectField_x3f(v_env_18_, v_induct_41_, v___x_43_);
if (lean_obj_tag(v___x_44_) == 0)
{
if (v___x_29_ == 0)
{
lean_del_object(v___x_39_);
goto v___jp_14_;
}
else
{
lean_object* v___x_45_; lean_object* v___x_47_; 
v___x_45_ = lean_box(0);
if (v_isShared_40_ == 0)
{
lean_ctor_set_tag(v___x_39_, 0);
lean_ctor_set(v___x_39_, 0, v___x_45_);
v___x_47_ = v___x_39_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v___x_45_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
else
{
lean_dec_ref_known(v___x_44_, 1);
lean_del_object(v___x_39_);
goto v___jp_14_;
}
}
}
else
{
lean_dec(v_val_36_);
lean_dec_ref(v_env_18_);
lean_dec_ref(v_str_12_);
goto v___jp_4_;
}
}
else
{
lean_dec(v___x_35_);
lean_dec_ref(v_env_18_);
lean_dec_ref(v_str_12_);
goto v___jp_4_;
}
}
}
}
else
{
lean_object* v___x_51_; lean_object* v___x_52_; 
lean_dec(v___x_19_);
lean_dec_ref(v_env_18_);
lean_dec_ref(v_str_12_);
v___x_51_ = lean_box(0);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
return v___x_52_;
}
v___jp_14_:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_15_ = l_Lean_Expr_appArg_x21(v_e_1_);
v___x_16_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
v___x_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
return v___x_17_;
}
}
else
{
lean_dec(v_declName_11_);
goto v___jp_7_;
}
}
else
{
lean_dec_ref(v___x_10_);
goto v___jp_7_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg___boxed(lean_object* v_e_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg(v_e_53_, v_a_54_);
lean_dec(v_a_54_);
lean_dec_ref(v_e_53_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg(lean_object* v_e_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg(v_e_57_, v_a_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___boxed(lean_object* v_e_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg(v_e_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
lean_dec_ref(v_e_64_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__6___redArg___lam__0(lean_object* v_k_71_, lean_object* v___y_72_, lean_object* v_b_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v___x_79_; 
lean_inc(v___y_77_);
lean_inc_ref(v___y_76_);
lean_inc(v___y_75_);
lean_inc_ref(v___y_74_);
lean_inc(v___y_72_);
v___x_79_ = lean_apply_7(v_k_71_, v_b_73_, v___y_72_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, lean_box(0));
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__6___redArg___lam__0___boxed(lean_object* v_k_80_, lean_object* v___y_81_, lean_object* v_b_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__6___redArg___lam__0(v_k_80_, v___y_81_, v_b_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_81_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__6___redArg(lean_object* v_name_89_, uint8_t v_bi_90_, lean_object* v_type_91_, lean_object* v_k_92_, uint8_t v_kind_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v___f_100_; lean_object* v___x_101_; 
lean_inc(v___y_94_);
v___f_100_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_100_, 0, v_k_92_);
lean_closure_set(v___f_100_, 1, v___y_94_);
v___x_101_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_89_, v_bi_90_, v_type_91_, v___f_100_, v_kind_93_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
if (lean_obj_tag(v___x_101_) == 0)
{
return v___x_101_;
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_101_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_101_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__6___redArg___boxed(lean_object* v_name_110_, lean_object* v_bi_111_, lean_object* v_type_112_, lean_object* v_k_113_, lean_object* v_kind_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
uint8_t v_bi_boxed_121_; uint8_t v_kind_boxed_122_; lean_object* v_res_123_; 
v_bi_boxed_121_ = lean_unbox(v_bi_111_);
v_kind_boxed_122_ = lean_unbox(v_kind_114_);
v_res_123_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__6___redArg(v_name_110_, v_bi_boxed_121_, v_type_112_, v_k_113_, v_kind_boxed_122_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__6(lean_object* v_00_u03b1_124_, lean_object* v_name_125_, uint8_t v_bi_126_, lean_object* v_type_127_, lean_object* v_k_128_, uint8_t v_kind_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__6___redArg(v_name_125_, v_bi_126_, v_type_127_, v_k_128_, v_kind_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__6___boxed(lean_object* v_00_u03b1_137_, lean_object* v_name_138_, lean_object* v_bi_139_, lean_object* v_type_140_, lean_object* v_k_141_, lean_object* v_kind_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
uint8_t v_bi_boxed_149_; uint8_t v_kind_boxed_150_; lean_object* v_res_151_; 
v_bi_boxed_149_ = lean_unbox(v_bi_139_);
v_kind_boxed_150_ = lean_unbox(v_kind_142_);
v_res_151_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__6(v_00_u03b1_137_, v_name_138_, v_bi_boxed_149_, v_type_140_, v_k_141_, v_kind_boxed_150_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(lean_object* v_m_152_, lean_object* v_query_153_, lean_object* v_x_154_, lean_object* v_x_155_, lean_object* v_x_156_){
_start:
{
lean_object* v_zero_157_; uint8_t v_isZero_158_; 
v_zero_157_ = lean_unsigned_to_nat(0u);
v_isZero_158_ = lean_nat_dec_eq(v_x_155_, v_zero_157_);
if (v_isZero_158_ == 1)
{
lean_dec(v_x_156_);
lean_dec(v_x_155_);
if (lean_obj_tag(v_x_154_) == 0)
{
lean_object* v___x_159_; 
v___x_159_ = lean_box(2);
return v___x_159_;
}
else
{
lean_object* v_val_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
v_val_160_ = lean_ctor_get(v_x_154_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v_x_154_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v_x_154_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_val_160_);
lean_dec(v_x_154_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_val_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
else
{
lean_object* v_keyArray_168_; lean_object* v_valueArray_169_; lean_object* v___x_170_; uint8_t v_isSome_171_; 
v_keyArray_168_ = lean_ctor_get(v_m_152_, 1);
v_valueArray_169_ = lean_ctor_get(v_m_152_, 2);
v___x_170_ = lean_array_fget_borrowed(v_keyArray_168_, v_x_156_);
v_isSome_171_ = lean_noption_is_some(v___x_170_);
if (v_isSome_171_ == 0)
{
lean_dec(v_x_155_);
if (lean_obj_tag(v_x_154_) == 0)
{
lean_object* v___x_172_; 
v___x_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_172_, 0, v_x_156_);
return v___x_172_;
}
else
{
lean_object* v_val_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
lean_dec(v_x_156_);
v_val_173_ = lean_ctor_get(v_x_154_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v_x_154_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v_x_154_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_val_173_);
lean_dec(v_x_154_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_val_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
else
{
lean_object* v_one_181_; lean_object* v_n_182_; lean_object* v___y_184_; 
v_one_181_ = lean_unsigned_to_nat(1u);
v_n_182_ = lean_nat_sub(v_x_155_, v_one_181_);
lean_dec(v_x_155_);
if (v_isSome_171_ == 0)
{
goto v___jp_190_;
}
else
{
lean_object* v___x_192_; uint8_t v_isSome_193_; 
v___x_192_ = lean_array_fget_borrowed(v_valueArray_169_, v_x_156_);
v_isSome_193_ = lean_noption_is_some(v___x_192_);
if (v_isSome_193_ == 0)
{
goto v___jp_190_;
}
else
{
lean_object* v_val_194_; uint8_t v___x_195_; 
lean_inc(v___x_170_);
v_val_194_ = lean_noption_get(v___x_170_);
v___x_195_ = lean_expr_eqv(v_val_194_, v_query_153_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
lean_dec(v_val_194_);
v___x_196_ = lean_array_get_size(v_keyArray_168_);
v___x_197_ = lean_nat_add(v_x_156_, v_one_181_);
lean_dec(v_x_156_);
v___x_198_ = lean_nat_dec_lt(v___x_197_, v___x_196_);
if (v___x_198_ == 0)
{
lean_dec(v___x_197_);
v_x_155_ = v_n_182_;
v_x_156_ = v_zero_157_;
goto _start;
}
else
{
v_x_155_ = v_n_182_;
v_x_156_ = v___x_197_;
goto _start;
}
}
else
{
lean_object* v_val_201_; lean_object* v___x_202_; 
lean_dec(v_n_182_);
lean_dec(v_x_154_);
lean_inc(v___x_192_);
v_val_201_ = lean_noption_get(v___x_192_);
v___x_202_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_202_, 0, v_x_156_);
lean_ctor_set(v___x_202_, 1, v_val_194_);
lean_ctor_set(v___x_202_, 2, v_val_201_);
return v___x_202_;
}
}
}
v___jp_183_:
{
lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_185_ = lean_array_get_size(v_keyArray_168_);
v___x_186_ = lean_nat_add(v_x_156_, v_one_181_);
lean_dec(v_x_156_);
v___x_187_ = lean_nat_dec_lt(v___x_186_, v___x_185_);
if (v___x_187_ == 0)
{
lean_dec(v___x_186_);
v_x_154_ = v___y_184_;
v_x_155_ = v_n_182_;
v_x_156_ = v_zero_157_;
goto _start;
}
else
{
v_x_154_ = v___y_184_;
v_x_155_ = v_n_182_;
v_x_156_ = v___x_186_;
goto _start;
}
}
v___jp_190_:
{
if (lean_obj_tag(v_x_154_) == 0)
{
lean_object* v___x_191_; 
lean_inc(v_x_156_);
v___x_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_191_, 0, v_x_156_);
v___y_184_ = v___x_191_;
goto v___jp_183_;
}
else
{
v___y_184_ = v_x_154_;
goto v___jp_183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg___boxed(lean_object* v_m_203_, lean_object* v_query_204_, lean_object* v_x_205_, lean_object* v_x_206_, lean_object* v_x_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_m_203_, v_query_204_, v_x_205_, v_x_206_, v_x_207_);
lean_dec_ref(v_query_204_);
lean_dec_ref(v_m_203_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(lean_object* v_m_209_, lean_object* v_query_210_){
_start:
{
lean_object* v_keyArray_211_; lean_object* v___x_212_; uint64_t v___x_213_; uint64_t v___x_214_; uint64_t v___x_215_; uint64_t v_fold_216_; uint64_t v___x_217_; uint64_t v___x_218_; uint64_t v___x_219_; size_t v___x_220_; size_t v___x_221_; size_t v___x_222_; size_t v___x_223_; size_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_keyArray_211_ = lean_ctor_get(v_m_209_, 1);
v___x_212_ = lean_array_get_size(v_keyArray_211_);
v___x_213_ = l_Lean_Expr_hash(v_query_210_);
v___x_214_ = 32ULL;
v___x_215_ = lean_uint64_shift_right(v___x_213_, v___x_214_);
v_fold_216_ = lean_uint64_xor(v___x_213_, v___x_215_);
v___x_217_ = 16ULL;
v___x_218_ = lean_uint64_shift_right(v_fold_216_, v___x_217_);
v___x_219_ = lean_uint64_xor(v_fold_216_, v___x_218_);
v___x_220_ = lean_uint64_to_usize(v___x_219_);
v___x_221_ = lean_usize_of_nat(v___x_212_);
v___x_222_ = ((size_t)1ULL);
v___x_223_ = lean_usize_sub(v___x_221_, v___x_222_);
v___x_224_ = lean_usize_land(v___x_220_, v___x_223_);
v___x_225_ = lean_usize_to_nat(v___x_224_);
v___x_226_ = lean_box(0);
v___x_227_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_m_209_, v_query_210_, v___x_226_, v___x_212_, v___x_225_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg___boxed(lean_object* v_m_228_, lean_object* v_query_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v_m_228_, v_query_229_);
lean_dec_ref(v_query_229_);
lean_dec_ref(v_m_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5_spec__7___redArg(lean_object* v_b_231_, lean_object* v_acc_232_, lean_object* v_i_233_){
_start:
{
lean_object* v___y_235_; lean_object* v_keyArray_243_; lean_object* v_valueArray_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v_keyArray_243_ = lean_ctor_get(v_b_231_, 1);
v_valueArray_244_ = lean_ctor_get(v_b_231_, 2);
v___x_245_ = lean_array_get_size(v_keyArray_243_);
v___x_246_ = lean_nat_dec_lt(v_i_233_, v___x_245_);
if (v___x_246_ == 0)
{
lean_dec(v_i_233_);
return v_acc_232_;
}
else
{
lean_object* v___x_247_; uint8_t v_isSome_248_; 
v___x_247_ = lean_array_fget_borrowed(v_keyArray_243_, v_i_233_);
v_isSome_248_ = lean_noption_is_some(v___x_247_);
if (v_isSome_248_ == 0)
{
goto v___jp_239_;
}
else
{
lean_object* v___x_249_; uint8_t v_isSome_250_; 
v___x_249_ = lean_array_fget_borrowed(v_valueArray_244_, v_i_233_);
v_isSome_250_ = lean_noption_is_some(v___x_249_);
if (v_isSome_250_ == 0)
{
goto v___jp_239_;
}
else
{
lean_object* v_val_251_; lean_object* v_val_252_; lean_object* v_i_254_; lean_object* v___x_259_; 
lean_inc(v___x_247_);
v_val_251_ = lean_noption_get(v___x_247_);
lean_inc(v___x_249_);
v_val_252_ = lean_noption_get(v___x_249_);
v___x_259_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v_acc_232_, v_val_251_);
switch(lean_obj_tag(v___x_259_))
{
case 0:
{
lean_object* v_index_260_; lean_object* v_size_261_; lean_object* v___x_262_; 
v_index_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_index_260_);
lean_dec_ref_known(v___x_259_, 3);
v_size_261_ = lean_ctor_get(v_acc_232_, 0);
lean_inc(v_size_261_);
v___x_262_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_232_, v_size_261_, v_index_260_, v_val_251_, v_val_252_);
lean_dec(v_index_260_);
v___y_235_ = v___x_262_;
goto v___jp_234_;
}
case 1:
{
lean_object* v_index_263_; 
v_index_263_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_index_263_);
lean_dec_ref_known(v___x_259_, 1);
v_i_254_ = v_index_263_;
goto v___jp_253_;
}
default: 
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_232_, v___x_264_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_index_266_; 
v_index_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_index_266_);
lean_dec_ref_known(v___x_265_, 1);
v_i_254_ = v_index_266_;
goto v___jp_253_;
}
else
{
lean_dec(v_val_252_);
lean_dec(v_val_251_);
v___y_235_ = v_acc_232_;
goto v___jp_234_;
}
}
}
v___jp_253_:
{
lean_object* v_size_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_size_255_ = lean_ctor_get(v_acc_232_, 0);
v___x_256_ = lean_unsigned_to_nat(1u);
v___x_257_ = lean_nat_add(v_size_255_, v___x_256_);
v___x_258_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_232_, v___x_257_, v_i_254_, v_val_251_, v_val_252_);
lean_dec(v_i_254_);
v___y_235_ = v___x_258_;
goto v___jp_234_;
}
}
}
}
v___jp_234_:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = lean_nat_add(v_i_233_, v___x_236_);
lean_dec(v_i_233_);
v_acc_232_ = v___y_235_;
v_i_233_ = v___x_237_;
goto _start;
}
v___jp_239_:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_nat_add(v_i_233_, v___x_240_);
lean_dec(v_i_233_);
v_i_233_ = v___x_241_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_b_267_, lean_object* v_acc_268_, lean_object* v_i_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5_spec__7___redArg(v_b_267_, v_acc_268_, v_i_269_);
lean_dec_ref(v_b_267_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5___redArg(lean_object* v_init_271_, lean_object* v_b_272_){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5_spec__7___redArg(v_b_272_, v_init_271_, v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5___redArg___boxed(lean_object* v_init_275_, lean_object* v_b_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5___redArg(v_init_275_, v_b_276_);
lean_dec_ref(v_b_276_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(lean_object* v_m_278_){
_start:
{
lean_object* v_keyArray_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v_cellCount_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v_target_286_; lean_object* v___x_287_; 
v_keyArray_279_ = lean_ctor_get(v_m_278_, 1);
v___x_280_ = lean_array_get_size(v_keyArray_279_);
v___x_281_ = lean_unsigned_to_nat(2u);
v_cellCount_282_ = lean_nat_mul(v___x_280_, v___x_281_);
v___x_283_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_282_);
v___x_284_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_282_);
v___x_285_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_282_);
v_target_286_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_286_, 0, v___x_283_);
lean_ctor_set(v_target_286_, 1, v___x_284_);
lean_ctor_set(v_target_286_, 2, v___x_285_);
v___x_287_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5___redArg(v_target_286_, v_m_278_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg___boxed(lean_object* v_m_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v_m_288_);
lean_dec_ref(v_m_288_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(lean_object* v_msgData_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v___x_296_; lean_object* v_env_297_; lean_object* v___x_298_; lean_object* v_mctx_299_; lean_object* v_lctx_300_; lean_object* v_options_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_296_ = lean_st_ref_get(v___y_294_);
v_env_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc_ref(v_env_297_);
lean_dec(v___x_296_);
v___x_298_ = lean_st_ref_get(v___y_292_);
v_mctx_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc_ref(v_mctx_299_);
lean_dec(v___x_298_);
v_lctx_300_ = lean_ctor_get(v___y_291_, 2);
v_options_301_ = lean_ctor_get(v___y_293_, 2);
lean_inc_ref(v_options_301_);
lean_inc_ref(v_lctx_300_);
v___x_302_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_302_, 0, v_env_297_);
lean_ctor_set(v___x_302_, 1, v_mctx_299_);
lean_ctor_set(v___x_302_, 2, v_lctx_300_);
lean_ctor_set(v___x_302_, 3, v_options_301_);
v___x_303_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v_msgData_290_);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0___boxed(lean_object* v_msgData_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msgData_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(lean_object* v_msg_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_ref_318_; lean_object* v___x_319_; lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_328_; 
v_ref_318_ = lean_ctor_get(v___y_315_, 5);
v___x_319_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msg_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
v_a_320_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_328_ == 0)
{
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_328_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_328_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v___x_326_; 
lean_inc(v_ref_318_);
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v_ref_318_);
lean_ctor_set(v___x_324_, 1, v_a_320_);
if (v_isShared_323_ == 0)
{
lean_ctor_set_tag(v___x_322_, 1);
lean_ctor_set(v___x_322_, 0, v___x_324_);
v___x_326_ = v___x_322_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_324_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg___boxed(lean_object* v_msg_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v_msg_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4_spec__7___redArg(lean_object* v_m_336_, lean_object* v_query_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v_m_336_, v_query_337_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_index_339_; lean_object* v_key_340_; lean_object* v_value_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
v_index_339_ = lean_ctor_get(v___x_338_, 0);
v_key_340_ = lean_ctor_get(v___x_338_, 1);
v_value_341_ = lean_ctor_get(v___x_338_, 2);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_338_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_value_341_);
lean_inc(v_key_340_);
lean_inc(v_index_339_);
lean_dec(v___x_338_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_index_339_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_key_340_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v_value_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
else
{
lean_object* v___x_349_; 
lean_dec(v___x_338_);
v___x_349_ = lean_box(1);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4_spec__7___redArg___boxed(lean_object* v_m_350_, lean_object* v_query_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4_spec__7___redArg(v_m_350_, v_query_351_);
lean_dec_ref(v_query_351_);
lean_dec_ref(v_m_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4___redArg(lean_object* v_m_353_, lean_object* v_a_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4_spec__7___redArg(v_m_353_, v_a_354_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_value_356_; lean_object* v___x_357_; 
v_value_356_ = lean_ctor_get(v___x_355_, 2);
lean_inc(v_value_356_);
lean_dec_ref_known(v___x_355_, 3);
v___x_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_357_, 0, v_value_356_);
return v___x_357_;
}
else
{
lean_object* v___x_358_; 
v___x_358_ = lean_box(0);
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4___redArg___boxed(lean_object* v_m_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4___redArg(v_m_359_, v_a_360_);
lean_dec_ref(v_a_360_);
lean_dec_ref(v_m_359_);
return v_res_361_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0(void){
_start:
{
lean_object* v___x_362_; lean_object* v_dummy_363_; 
v___x_362_ = lean_box(0);
v_dummy_363_ = l_Lean_Expr_sort___override(v___x_362_);
return v_dummy_363_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__0));
v___x_366_ = l_Lean_stringToMessageData(v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(lean_object* v_args_367_, lean_object* v_a_368_, lean_object* v_snd_369_, lean_object* v_____r_370_, lean_object* v_fty_371_, lean_object* v_j_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
if (lean_obj_tag(v_fty_371_) == 7)
{
lean_object* v_body_379_; uint8_t v_binderInfo_380_; lean_object* v___x_381_; uint8_t v_a_383_; uint8_t v___x_442_; 
v_body_379_ = lean_ctor_get(v_fty_371_, 2);
lean_inc_ref(v_body_379_);
v_binderInfo_380_ = lean_ctor_get_uint8(v_fty_371_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_fty_371_, 3);
v___x_381_ = lean_array_fget_borrowed(v_args_367_, v_a_368_);
v___x_442_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_380_);
if (v___x_442_ == 0)
{
uint8_t v___x_443_; 
v___x_443_ = l_Lean_Expr_isSort(v___x_381_);
if (v___x_443_ == 0)
{
goto v___jp_430_;
}
else
{
if (v___x_442_ == 0)
{
v_a_383_ = v___x_442_;
goto v___jp_382_;
}
else
{
goto v___jp_430_;
}
}
}
else
{
v_a_383_ = v___x_442_;
goto v___jp_382_;
}
v___jp_382_:
{
if (v_a_383_ == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
lean_inc(v_j_372_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_j_372_);
lean_ctor_set(v___x_384_, 1, v_snd_369_);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v_body_379_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
else
{
lean_object* v___x_388_; 
lean_inc(v___x_381_);
v___x_388_ = l_Lean_Meta_isProof(v___x_381_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_421_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_421_ == 0)
{
v___x_391_ = v___x_388_;
v_isShared_392_ = v_isSharedCheck_421_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_388_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_421_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
uint8_t v___x_393_; 
v___x_393_ = lean_unbox(v_a_389_);
lean_dec(v_a_389_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
lean_del_object(v___x_391_);
lean_inc(v___x_381_);
v___x_394_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_381_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_406_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_406_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_406_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_406_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_399_ = l_Lean_Expr_app___override(v_snd_369_, v_a_395_);
lean_inc(v_j_372_);
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v_j_372_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v_body_379_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_402_);
v___x_404_ = v___x_397_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec_ref(v_body_379_);
lean_dec(v_snd_369_);
v_a_407_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_394_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_394_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
else
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
lean_inc(v_j_372_);
v___x_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_415_, 0, v_j_372_);
lean_ctor_set(v___x_415_, 1, v_snd_369_);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v_body_379_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v___x_417_);
v___x_419_ = v___x_391_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec_ref(v_body_379_);
lean_dec(v_snd_369_);
v_a_422_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_388_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_388_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
v___jp_430_:
{
lean_object* v___x_431_; 
lean_inc(v___x_381_);
v___x_431_ = l_Lean_Meta_isTypeFormer(v___x_381_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; uint8_t v___x_433_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_a_432_);
lean_dec_ref_known(v___x_431_, 1);
v___x_433_ = lean_unbox(v_a_432_);
lean_dec(v_a_432_);
v_a_383_ = v___x_433_;
goto v___jp_382_;
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec_ref(v_body_379_);
lean_dec(v_snd_369_);
v_a_434_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_431_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_431_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
}
else
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1);
v___x_445_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v___x_444_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_455_; 
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_455_ == 0)
{
lean_object* v_unused_456_; 
v_unused_456_ = lean_ctor_get(v___x_445_, 0);
lean_dec(v_unused_456_);
v___x_447_ = v___x_445_;
v_isShared_448_ = v_isSharedCheck_455_;
goto v_resetjp_446_;
}
else
{
lean_dec(v___x_445_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_455_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_453_; 
lean_inc(v_j_372_);
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v_j_372_);
lean_ctor_set(v___x_449_, 1, v_snd_369_);
v___x_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_450_, 0, v_fty_371_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_451_);
v___x_453_ = v___x_447_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec_ref(v_fty_371_);
lean_dec(v_snd_369_);
v_a_457_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_445_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_445_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(lean_object* v_upperBound_465_, lean_object* v_args_466_, lean_object* v_a_467_, lean_object* v_b_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v___y_476_; uint8_t v___x_498_; 
v___x_498_ = lean_nat_dec_lt(v_a_467_, v_upperBound_465_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
lean_dec(v_a_467_);
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v_b_468_);
return v___x_499_;
}
else
{
lean_object* v_snd_500_; lean_object* v_fst_501_; lean_object* v_fst_502_; lean_object* v_snd_503_; lean_object* v_a_505_; uint8_t v___x_508_; 
v_snd_500_ = lean_ctor_get(v_b_468_, 1);
lean_inc(v_snd_500_);
v_fst_501_ = lean_ctor_get(v_b_468_, 0);
lean_inc(v_fst_501_);
lean_dec_ref(v_b_468_);
v_fst_502_ = lean_ctor_get(v_snd_500_, 0);
lean_inc(v_fst_502_);
v_snd_503_ = lean_ctor_get(v_snd_500_, 1);
lean_inc(v_snd_503_);
lean_dec(v_snd_500_);
v___x_508_ = l_Lean_Expr_isForall(v_fst_501_);
if (v___x_508_ == 0)
{
lean_object* v_keyedConfig_509_; uint8_t v_trackZetaDelta_510_; lean_object* v_zetaDeltaSet_511_; lean_object* v_lctx_512_; lean_object* v_localInstances_513_; lean_object* v_defEqCtx_x3f_514_; lean_object* v_synthPendingDepth_515_; lean_object* v_customCanUnfoldPredicate_x3f_516_; uint8_t v_univApprox_517_; uint8_t v_inTypeClassResolution_518_; uint8_t v_cacheInferType_519_; uint8_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_keyedConfig_509_ = lean_ctor_get(v___y_470_, 0);
v_trackZetaDelta_510_ = lean_ctor_get_uint8(v___y_470_, sizeof(void*)*7);
v_zetaDeltaSet_511_ = lean_ctor_get(v___y_470_, 1);
v_lctx_512_ = lean_ctor_get(v___y_470_, 2);
v_localInstances_513_ = lean_ctor_get(v___y_470_, 3);
v_defEqCtx_x3f_514_ = lean_ctor_get(v___y_470_, 4);
v_synthPendingDepth_515_ = lean_ctor_get(v___y_470_, 5);
v_customCanUnfoldPredicate_x3f_516_ = lean_ctor_get(v___y_470_, 6);
v_univApprox_517_ = lean_ctor_get_uint8(v___y_470_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_518_ = lean_ctor_get_uint8(v___y_470_, sizeof(void*)*7 + 2);
v_cacheInferType_519_ = lean_ctor_get_uint8(v___y_470_, sizeof(void*)*7 + 3);
v___x_520_ = 0;
v___x_521_ = lean_expr_instantiate_rev_range(v_fst_501_, v_fst_502_, v_a_467_, v_args_466_);
lean_dec(v_fst_502_);
lean_dec(v_fst_501_);
lean_inc_ref(v_keyedConfig_509_);
v___x_522_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_520_, v_keyedConfig_509_);
lean_inc(v_customCanUnfoldPredicate_x3f_516_);
lean_inc(v_synthPendingDepth_515_);
lean_inc(v_defEqCtx_x3f_514_);
lean_inc_ref(v_localInstances_513_);
lean_inc_ref(v_lctx_512_);
lean_inc(v_zetaDeltaSet_511_);
v___x_523_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_523_, 0, v___x_522_);
lean_ctor_set(v___x_523_, 1, v_zetaDeltaSet_511_);
lean_ctor_set(v___x_523_, 2, v_lctx_512_);
lean_ctor_set(v___x_523_, 3, v_localInstances_513_);
lean_ctor_set(v___x_523_, 4, v_defEqCtx_x3f_514_);
lean_ctor_set(v___x_523_, 5, v_synthPendingDepth_515_);
lean_ctor_set(v___x_523_, 6, v_customCanUnfoldPredicate_x3f_516_);
lean_ctor_set_uint8(v___x_523_, sizeof(void*)*7, v_trackZetaDelta_510_);
lean_ctor_set_uint8(v___x_523_, sizeof(void*)*7 + 1, v_univApprox_517_);
lean_ctor_set_uint8(v___x_523_, sizeof(void*)*7 + 2, v_inTypeClassResolution_518_);
lean_ctor_set_uint8(v___x_523_, sizeof(void*)*7 + 3, v_cacheInferType_519_);
lean_inc(v___y_473_);
lean_inc_ref(v___y_472_);
lean_inc(v___y_471_);
v___x_524_ = lean_whnf(v___x_521_, v___x_523_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v___x_524_, 1);
v_a_505_ = v_a_525_;
goto v___jp_504_;
}
else
{
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_526_; 
v_a_526_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_524_, 1);
v_a_505_ = v_a_526_;
goto v___jp_504_;
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec(v_snd_503_);
lean_dec(v_a_467_);
v_a_527_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_524_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_524_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_box(0);
v___x_536_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_args_466_, v_a_467_, v_snd_503_, v___x_535_, v_fst_501_, v_fst_502_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
lean_dec(v_fst_502_);
v___y_476_ = v___x_536_;
goto v___jp_475_;
}
v___jp_504_:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_box(0);
v___x_507_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_args_466_, v_a_467_, v_snd_503_, v___x_506_, v_a_505_, v_a_467_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
v___y_476_ = v___x_507_;
goto v___jp_475_;
}
}
v___jp_475_:
{
if (lean_obj_tag(v___y_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_489_; 
v_a_477_ = lean_ctor_get(v___y_476_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___y_476_);
if (v_isSharedCheck_489_ == 0)
{
v___x_479_ = v___y_476_;
v_isShared_480_ = v_isSharedCheck_489_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___y_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_489_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
if (lean_obj_tag(v_a_477_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_483_; 
lean_dec(v_a_467_);
v_a_481_ = lean_ctor_get(v_a_477_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v_a_477_, 1);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v_a_481_);
v___x_483_ = v___x_479_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
lean_del_object(v___x_479_);
v_a_485_ = lean_ctor_get(v_a_477_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v_a_477_, 1);
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_nat_add(v_a_467_, v___x_486_);
lean_dec(v_a_467_);
v_a_467_ = v___x_487_;
v_b_468_ = v_a_485_;
goto _start;
}
}
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec(v_a_467_);
v_a_490_ = lean_ctor_get(v___y_476_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___y_476_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___y_476_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___y_476_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5(lean_object* v_x_537_, lean_object* v_x_538_, lean_object* v_x_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
if (lean_obj_tag(v_x_537_) == 5)
{
lean_object* v_fn_546_; lean_object* v_arg_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v_fn_546_ = lean_ctor_get(v_x_537_, 0);
lean_inc_ref(v_fn_546_);
v_arg_547_ = lean_ctor_get(v_x_537_, 1);
lean_inc_ref(v_arg_547_);
lean_dec_ref_known(v_x_537_, 2);
v___x_548_ = lean_array_set(v_x_538_, v_x_539_, v_arg_547_);
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = lean_nat_sub(v_x_539_, v___x_549_);
lean_dec(v_x_539_);
v_x_537_ = v_fn_546_;
v_x_538_ = v___x_548_;
v_x_539_ = v___x_550_;
goto _start;
}
else
{
lean_object* v___x_552_; 
lean_dec(v_x_539_);
lean_inc(v___y_544_);
lean_inc_ref(v___y_543_);
lean_inc(v___y_542_);
lean_inc_ref(v___y_541_);
lean_inc_ref(v_x_537_);
v___x_552_ = lean_infer_type(v_x_537_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_554_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_552_, 1);
v___x_554_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_x_537_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v___x_554_, 1);
v___x_556_ = lean_array_get_size(v_x_538_);
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v_a_555_);
v___x_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_559_, 0, v_a_553_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v___x_556_, v_x_538_, v___x_557_, v___x_559_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec_ref(v_x_538_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_570_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_570_ == 0)
{
v___x_563_ = v___x_560_;
v_isShared_564_ = v_isSharedCheck_570_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_570_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v_snd_565_; lean_object* v_snd_566_; lean_object* v___x_568_; 
v_snd_565_ = lean_ctor_get(v_a_561_, 1);
lean_inc(v_snd_565_);
lean_dec(v_a_561_);
v_snd_566_ = lean_ctor_get(v_snd_565_, 1);
lean_inc(v_snd_566_);
lean_dec(v_snd_565_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v_snd_566_);
v___x_568_ = v___x_563_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_snd_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
v_a_571_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_560_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_560_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
else
{
lean_dec(v_a_553_);
lean_dec_ref(v_x_538_);
return v___x_554_;
}
}
else
{
lean_dec_ref(v_x_538_);
lean_dec_ref(v_x_537_);
return v___x_552_;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = l_Lean_Expr_bvar___override(v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0(lean_object* v_body_581_, lean_object* v_binderName_582_, uint8_t v_binderInfo_583_, lean_object* v_binderType_584_, lean_object* v_arg_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_ty_x27_593_; uint8_t v___x_605_; 
v___x_605_ = l_Lean_Expr_hasLooseBVars(v_body_581_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; 
v___x_606_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_binderType_584_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref_known(v___x_606_, 1);
v_ty_x27_593_ = v_a_607_;
goto v___jp_592_;
}
else
{
lean_dec(v_binderName_582_);
return v___x_606_;
}
}
else
{
lean_object* v___x_608_; 
lean_dec_ref(v_binderType_584_);
v___x_608_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0);
v_ty_x27_593_ = v___x_608_;
goto v___jp_592_;
}
v___jp_592_:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = lean_expr_instantiate1(v_body_581_, v_arg_585_);
v___x_595_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_594_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_604_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_604_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = l_Lean_Expr_forallE___override(v_binderName_582_, v_ty_x27_593_, v_a_596_, v_binderInfo_583_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_600_);
v___x_602_ = v___x_598_;
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
else
{
lean_dec_ref(v_ty_x27_593_);
lean_dec(v_binderName_582_);
return v___x_595_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___boxed(lean_object* v_body_609_, lean_object* v_binderName_610_, lean_object* v_binderInfo_611_, lean_object* v_binderType_612_, lean_object* v_arg_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
uint8_t v_binderInfo_19229__boxed_620_; lean_object* v_res_621_; 
v_binderInfo_19229__boxed_620_ = lean_unbox(v_binderInfo_611_);
v_res_621_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0(v_body_609_, v_binderName_610_, v_binderInfo_19229__boxed_620_, v_binderType_612_, v_arg_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v_arg_613_);
lean_dec_ref(v_body_609_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1___boxed(lean_object* v_body_622_, lean_object* v_arg_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1(v_body_622_, v_arg_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v_arg_623_);
lean_dec_ref(v_body_622_);
return v_res_630_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__2));
v___x_635_ = l_Lean_Level_param___override(v___x_634_);
return v___x_635_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3);
v___x_637_ = l_Lean_Expr_sort___override(v___x_636_);
return v___x_637_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_box(0);
v___x_639_ = l_Lean_Level_succ___override(v___x_638_);
return v___x_639_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5);
v___x_641_ = l_Lean_Expr_sort___override(v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(lean_object* v_e_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v_i_657_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v_i_676_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v_a_694_; lean_object* v___y_727_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_st_ref_get(v_a_643_);
v___x_730_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4___redArg(v___x_729_, v_e_642_);
lean_dec(v___x_729_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v___x_731_; 
lean_inc_ref(v_e_642_);
v___x_731_ = l_Lean_Meta_isProof(v_e_642_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; uint8_t v___x_733_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref_known(v___x_731_, 1);
v___x_733_ = lean_unbox(v_a_732_);
lean_dec(v_a_732_);
if (v___x_733_ == 0)
{
switch(lean_obj_tag(v_e_642_))
{
case 5:
{
lean_object* v___x_734_; 
v___x_734_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg(v_e_642_, v_a_647_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
if (lean_obj_tag(v_a_735_) == 1)
{
lean_object* v_val_736_; lean_object* v___x_737_; 
v_val_736_ = lean_ctor_get(v_a_735_, 0);
lean_inc(v_val_736_);
lean_dec_ref_known(v_a_735_, 1);
v___x_737_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_val_736_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
v___y_727_ = v___x_737_;
goto v___jp_726_;
}
else
{
lean_object* v_dummy_738_; lean_object* v_nargs_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
lean_dec(v_a_735_);
v_dummy_738_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0);
v_nargs_739_ = l_Lean_Expr_getAppNumArgs(v_e_642_);
lean_inc(v_nargs_739_);
v___x_740_ = lean_mk_array(v_nargs_739_, v_dummy_738_);
v___x_741_ = lean_unsigned_to_nat(1u);
v___x_742_ = lean_nat_sub(v_nargs_739_, v___x_741_);
lean_dec(v_nargs_739_);
lean_inc_ref(v_e_642_);
v___x_743_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5(v_e_642_, v___x_740_, v___x_742_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
v___y_727_ = v___x_743_;
goto v___jp_726_;
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec_ref_known(v_e_642_, 2);
v_a_744_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_734_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_734_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
case 7:
{
lean_object* v_binderName_752_; lean_object* v_binderType_753_; lean_object* v_body_754_; uint8_t v_binderInfo_755_; lean_object* v___x_756_; lean_object* v___f_757_; uint8_t v___x_758_; lean_object* v___x_759_; 
v_binderName_752_ = lean_ctor_get(v_e_642_, 0);
v_binderType_753_ = lean_ctor_get(v_e_642_, 1);
v_body_754_ = lean_ctor_get(v_e_642_, 2);
v_binderInfo_755_ = lean_ctor_get_uint8(v_e_642_, sizeof(void*)*3 + 8);
v___x_756_ = lean_box(v_binderInfo_755_);
lean_inc_ref_n(v_binderType_753_, 2);
lean_inc_n(v_binderName_752_, 2);
lean_inc_ref(v_body_754_);
v___f_757_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___boxed), 11, 4);
lean_closure_set(v___f_757_, 0, v_body_754_);
lean_closure_set(v___f_757_, 1, v_binderName_752_);
lean_closure_set(v___f_757_, 2, v___x_756_);
lean_closure_set(v___f_757_, 3, v_binderType_753_);
v___x_758_ = 0;
v___x_759_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__6___redArg(v_binderName_752_, v_binderInfo_755_, v_binderType_753_, v___f_757_, v___x_758_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
v___y_727_ = v___x_759_;
goto v___jp_726_;
}
case 6:
{
lean_object* v_binderName_760_; lean_object* v_binderType_761_; lean_object* v_body_762_; uint8_t v_binderInfo_763_; lean_object* v___x_764_; 
v_binderName_760_ = lean_ctor_get(v_e_642_, 0);
v_binderType_761_ = lean_ctor_get(v_e_642_, 1);
v_body_762_ = lean_ctor_get(v_e_642_, 2);
v_binderInfo_763_ = lean_ctor_get_uint8(v_e_642_, sizeof(void*)*3 + 8);
lean_inc_ref(v_e_642_);
v___x_764_ = l_Lean_Expr_etaExpandedStrict_x3f(v_e_642_);
if (lean_obj_tag(v___x_764_) == 1)
{
lean_object* v_val_765_; lean_object* v___x_766_; 
v_val_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_val_765_);
lean_dec_ref_known(v___x_764_, 1);
v___x_766_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_val_765_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
v___y_727_ = v___x_766_;
goto v___jp_726_;
}
else
{
lean_object* v___f_767_; uint8_t v___x_768_; lean_object* v___x_769_; 
lean_dec(v___x_764_);
lean_inc_ref(v_body_762_);
v___f_767_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1___boxed), 8, 1);
lean_closure_set(v___f_767_, 0, v_body_762_);
v___x_768_ = 0;
lean_inc_ref(v_binderType_761_);
lean_inc(v_binderName_760_);
v___x_769_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__6___redArg(v_binderName_760_, v_binderInfo_763_, v_binderType_761_, v___f_767_, v___x_768_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
v___y_727_ = v___x_769_;
goto v___jp_726_;
}
}
case 8:
{
lean_object* v_value_770_; lean_object* v_body_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v_value_770_ = lean_ctor_get(v_e_642_, 2);
v_body_771_ = lean_ctor_get(v_e_642_, 3);
v___x_772_ = lean_expr_instantiate1(v_body_771_, v_value_770_);
v___x_773_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_772_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
v___y_727_ = v___x_773_;
goto v___jp_726_;
}
case 3:
{
uint8_t v___x_774_; 
v___x_774_ = l_Lean_Expr_isProp(v_e_642_);
if (v___x_774_ == 0)
{
uint8_t v___x_775_; 
v___x_775_ = l_Lean_Expr_isType(v_e_642_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
v___x_776_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4);
v_a_694_ = v___x_776_;
goto v___jp_693_;
}
else
{
lean_object* v___x_777_; 
v___x_777_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6);
v_a_694_ = v___x_777_;
goto v___jp_693_;
}
}
else
{
lean_object* v___x_778_; 
v___x_778_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0);
v_a_694_ = v___x_778_;
goto v___jp_693_;
}
}
case 4:
{
lean_object* v_declName_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_declName_779_ = lean_ctor_get(v_e_642_, 0);
v___x_780_ = lean_box(0);
lean_inc(v_declName_779_);
v___x_781_ = l_Lean_Expr_const___override(v_declName_779_, v___x_780_);
v_a_694_ = v___x_781_;
goto v___jp_693_;
}
case 10:
{
lean_object* v_expr_782_; lean_object* v___x_783_; 
v_expr_782_ = lean_ctor_get(v_e_642_, 1);
lean_inc_ref(v_expr_782_);
v___x_783_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_expr_782_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
v___y_727_ = v___x_783_;
goto v___jp_726_;
}
default: 
{
lean_object* v___x_784_; 
v___x_784_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0);
v_a_694_ = v___x_784_;
goto v___jp_693_;
}
}
}
else
{
lean_object* v___x_785_; 
v___x_785_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0);
v_a_694_ = v___x_785_;
goto v___jp_693_;
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec_ref(v_e_642_);
v_a_786_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_731_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_731_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
lean_object* v_val_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec_ref(v_e_642_);
v_val_794_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_730_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_val_794_);
lean_dec(v___x_730_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set_tag(v___x_796_, 0);
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_val_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
v___jp_649_:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_st_ref_put(v_a_643_, v___y_651_);
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___y_650_);
return v___x_653_;
}
v___jp_654_:
{
lean_object* v_size_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v_size_658_ = lean_ctor_get(v___y_655_, 0);
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = lean_nat_add(v_size_658_, v___x_659_);
lean_inc_ref(v___y_656_);
v___x_661_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_655_, v___x_660_, v_i_657_, v_e_642_, v___y_656_);
lean_dec(v_i_657_);
v___y_650_ = v___y_656_;
v___y_651_ = v___x_661_;
goto v___jp_649_;
}
v___jp_662_:
{
lean_object* v___x_665_; 
v___x_665_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v___y_664_, v_e_642_);
switch(lean_obj_tag(v___x_665_))
{
case 0:
{
lean_object* v_index_666_; lean_object* v_size_667_; lean_object* v___x_668_; 
v_index_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_index_666_);
lean_dec_ref_known(v___x_665_, 3);
v_size_667_ = lean_ctor_get(v___y_664_, 0);
lean_inc(v_size_667_);
lean_inc_ref(v___y_663_);
v___x_668_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_664_, v_size_667_, v_index_666_, v_e_642_, v___y_663_);
lean_dec(v_index_666_);
v___y_650_ = v___y_663_;
v___y_651_ = v___x_668_;
goto v___jp_649_;
}
case 1:
{
lean_object* v_index_669_; 
v_index_669_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_index_669_);
lean_dec_ref_known(v___x_665_, 1);
v___y_655_ = v___y_664_;
v___y_656_ = v___y_663_;
v_i_657_ = v_index_669_;
goto v___jp_654_;
}
default: 
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_664_, v___x_670_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_index_672_; 
v_index_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_index_672_);
lean_dec_ref_known(v___x_671_, 1);
v___y_655_ = v___y_664_;
v___y_656_ = v___y_663_;
v_i_657_ = v_index_672_;
goto v___jp_654_;
}
else
{
lean_dec_ref(v_e_642_);
v___y_650_ = v___y_663_;
v___y_651_ = v___y_664_;
goto v___jp_649_;
}
}
}
}
v___jp_673_:
{
lean_object* v_size_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v_size_677_ = lean_ctor_get(v___y_675_, 0);
v___x_678_ = lean_unsigned_to_nat(1u);
v___x_679_ = lean_nat_add(v_size_677_, v___x_678_);
lean_inc_ref(v___y_674_);
v___x_680_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_675_, v___x_679_, v_i_676_, v_e_642_, v___y_674_);
lean_dec(v_i_676_);
v___y_650_ = v___y_674_;
v___y_651_ = v___x_680_;
goto v___jp_649_;
}
v___jp_681_:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v___y_683_);
lean_dec_ref(v___y_683_);
v___x_685_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v___x_684_, v_e_642_);
switch(lean_obj_tag(v___x_685_))
{
case 0:
{
lean_object* v_index_686_; lean_object* v_size_687_; lean_object* v___x_688_; 
v_index_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_index_686_);
lean_dec_ref_known(v___x_685_, 3);
v_size_687_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_size_687_);
lean_inc_ref(v___y_682_);
v___x_688_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_684_, v_size_687_, v_index_686_, v_e_642_, v___y_682_);
lean_dec(v_index_686_);
v___y_650_ = v___y_682_;
v___y_651_ = v___x_688_;
goto v___jp_649_;
}
case 1:
{
lean_object* v_index_689_; 
v_index_689_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_index_689_);
lean_dec_ref_known(v___x_685_, 1);
v___y_674_ = v___y_682_;
v___y_675_ = v___x_684_;
v_i_676_ = v_index_689_;
goto v___jp_673_;
}
default: 
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_684_, v___x_690_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_index_692_; 
v_index_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_index_692_);
lean_dec_ref_known(v___x_691_, 1);
v___y_674_ = v___y_682_;
v___y_675_ = v___x_684_;
v_i_676_ = v_index_692_;
goto v___jp_673_;
}
else
{
lean_dec_ref(v_e_642_);
v___y_650_ = v___y_682_;
v___y_651_ = v___x_684_;
goto v___jp_649_;
}
}
}
}
v___jp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_st_ref_take(v_a_643_);
v___x_696_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v___x_695_, v_e_642_);
switch(lean_obj_tag(v___x_696_))
{
case 0:
{
lean_object* v_index_697_; lean_object* v_size_698_; lean_object* v___x_699_; 
v_index_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_index_697_);
lean_dec_ref_known(v___x_696_, 3);
v_size_698_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_size_698_);
lean_inc_ref(v_a_694_);
v___x_699_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_695_, v_size_698_, v_index_697_, v_e_642_, v_a_694_);
lean_dec(v_index_697_);
v___y_650_ = v_a_694_;
v___y_651_ = v___x_699_;
goto v___jp_649_;
}
case 1:
{
lean_object* v_index_700_; lean_object* v_size_701_; lean_object* v_keyArray_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v_index_700_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_index_700_);
lean_dec_ref_known(v___x_696_, 1);
v_size_701_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_size_701_);
v_keyArray_702_ = lean_ctor_get(v___x_695_, 1);
lean_inc_ref(v_keyArray_702_);
v___x_703_ = lean_unsigned_to_nat(1u);
v___x_704_ = lean_nat_add(v_size_701_, v___x_703_);
lean_dec(v_size_701_);
v___x_705_ = lean_array_get_size(v_keyArray_702_);
lean_dec_ref(v_keyArray_702_);
v___x_706_ = lean_nat_dec_lt(v___x_704_, v___x_705_);
if (v___x_706_ == 0)
{
lean_dec(v___x_704_);
lean_dec(v_index_700_);
v___y_682_ = v_a_694_;
v___y_683_ = v___x_695_;
goto v___jp_681_;
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_707_ = lean_unsigned_to_nat(4u);
v___x_708_ = lean_nat_mul(v___x_704_, v___x_707_);
v___x_709_ = lean_unsigned_to_nat(3u);
v___x_710_ = lean_nat_mul(v___x_705_, v___x_709_);
v___x_711_ = lean_nat_dec_le(v___x_708_, v___x_710_);
lean_dec(v___x_710_);
lean_dec(v___x_708_);
if (v___x_711_ == 0)
{
lean_dec(v___x_704_);
lean_dec(v_index_700_);
v___y_682_ = v_a_694_;
v___y_683_ = v___x_695_;
goto v___jp_681_;
}
else
{
lean_object* v___x_712_; 
lean_inc_ref(v_a_694_);
v___x_712_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_695_, v___x_704_, v_index_700_, v_e_642_, v_a_694_);
lean_dec(v_index_700_);
v___y_650_ = v_a_694_;
v___y_651_ = v___x_712_;
goto v___jp_649_;
}
}
}
default: 
{
lean_object* v_size_713_; lean_object* v_keyArray_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v_size_713_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_size_713_);
v_keyArray_714_ = lean_ctor_get(v___x_695_, 1);
lean_inc_ref(v_keyArray_714_);
v___x_715_ = lean_unsigned_to_nat(1u);
v___x_716_ = lean_nat_add(v_size_713_, v___x_715_);
lean_dec(v_size_713_);
v___x_717_ = lean_array_get_size(v_keyArray_714_);
lean_dec_ref(v_keyArray_714_);
v___x_718_ = lean_nat_dec_lt(v___x_716_, v___x_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; 
lean_dec(v___x_716_);
v___x_719_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v___x_695_);
lean_dec(v___x_695_);
v___y_663_ = v_a_694_;
v___y_664_ = v___x_719_;
goto v___jp_662_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_720_ = lean_unsigned_to_nat(4u);
v___x_721_ = lean_nat_mul(v___x_716_, v___x_720_);
lean_dec(v___x_716_);
v___x_722_ = lean_unsigned_to_nat(3u);
v___x_723_ = lean_nat_mul(v___x_717_, v___x_722_);
v___x_724_ = lean_nat_dec_le(v___x_721_, v___x_723_);
lean_dec(v___x_723_);
lean_dec(v___x_721_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
v___x_725_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v___x_695_);
lean_dec(v___x_695_);
v___y_663_ = v_a_694_;
v___y_664_ = v___x_725_;
goto v___jp_662_;
}
else
{
v___y_663_ = v_a_694_;
v___y_664_ = v___x_695_;
goto v___jp_662_;
}
}
}
}
}
v___jp_726_:
{
if (lean_obj_tag(v___y_727_) == 0)
{
lean_object* v_a_728_; 
v_a_728_ = lean_ctor_get(v___y_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v___y_727_, 1);
v_a_694_ = v_a_728_;
goto v___jp_693_;
}
else
{
lean_dec_ref(v_e_642_);
return v___y_727_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1(lean_object* v_body_802_, lean_object* v_arg_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_expr_instantiate1(v_body_802_, v_arg_803_);
v___x_811_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_810_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___boxed(lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5(v_x_812_, v_x_813_, v_x_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___boxed(lean_object* v_upperBound_822_, lean_object* v_args_823_, lean_object* v_a_824_, lean_object* v_b_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v_upperBound_822_, v_args_823_, v_a_824_, v_b_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v_args_823_);
lean_dec(v_upperBound_822_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___boxed(lean_object* v_args_833_, lean_object* v_a_834_, lean_object* v_snd_835_, lean_object* v_____r_836_, lean_object* v_fty_837_, lean_object* v_j_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_args_833_, v_a_834_, v_snd_835_, v_____r_836_, v_fty_837_, v_j_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec(v_j_838_);
lean_dec(v_a_834_);
lean_dec_ref(v_args_833_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___boxed(lean_object* v_e_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_e_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0(lean_object* v_00_u03b1_854_, lean_object* v_msg_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v_msg_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___boxed(lean_object* v_00_u03b1_862_, lean_object* v_msg_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0(v_00_u03b1_862_, v_msg_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1(lean_object* v_upperBound_870_, lean_object* v_args_871_, lean_object* v_inst_872_, lean_object* v_R_873_, lean_object* v_a_874_, lean_object* v_b_875_, lean_object* v_c_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v_upperBound_870_, v_args_871_, v_a_874_, v_b_875_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___boxed(lean_object* v_upperBound_884_, lean_object* v_args_885_, lean_object* v_inst_886_, lean_object* v_R_887_, lean_object* v_a_888_, lean_object* v_b_889_, lean_object* v_c_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1(v_upperBound_884_, v_args_885_, v_inst_886_, v_R_887_, v_a_888_, v_b_889_, v_c_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v_args_885_);
lean_dec(v_upperBound_884_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2(lean_object* v_00_u03b2_898_, lean_object* v_m_899_, lean_object* v_query_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v_m_899_, v_query_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___boxed(lean_object* v_00_u03b2_902_, lean_object* v_m_903_, lean_object* v_query_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2(v_00_u03b2_902_, v_m_903_, v_query_904_);
lean_dec_ref(v_query_904_);
lean_dec_ref(v_m_903_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3(lean_object* v_00_u03b2_906_, lean_object* v_m_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v_m_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___boxed(lean_object* v_00_u03b2_909_, lean_object* v_m_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3(v_00_u03b2_909_, v_m_910_);
lean_dec_ref(v_m_910_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(lean_object* v_00_u03b2_912_, lean_object* v_m_913_, lean_object* v_a_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4___redArg(v_m_913_, v_a_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4___boxed(lean_object* v_00_u03b2_916_, lean_object* v_m_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(v_00_u03b2_916_, v_m_917_, v_a_918_);
lean_dec_ref(v_a_918_);
lean_dec_ref(v_m_917_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3(lean_object* v_00_u03b2_920_, lean_object* v_m_921_, lean_object* v_query_922_, lean_object* v_x_923_, lean_object* v_x_924_, lean_object* v_x_925_, lean_object* v_x_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_m_921_, v_query_922_, v_x_923_, v_x_924_, v_x_925_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___boxed(lean_object* v_00_u03b2_928_, lean_object* v_m_929_, lean_object* v_query_930_, lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v_x_933_, lean_object* v_x_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3(v_00_u03b2_928_, v_m_929_, v_query_930_, v_x_931_, v_x_932_, v_x_933_, v_x_934_);
lean_dec_ref(v_query_930_);
lean_dec_ref(v_m_929_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5(lean_object* v_00_u03b2_936_, lean_object* v_init_937_, lean_object* v_b_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5___redArg(v_init_937_, v_b_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5___boxed(lean_object* v_00_u03b2_940_, lean_object* v_init_941_, lean_object* v_b_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5(v_00_u03b2_940_, v_init_941_, v_b_942_);
lean_dec_ref(v_b_942_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4_spec__7(lean_object* v_00_u03b2_944_, lean_object* v_m_945_, lean_object* v_query_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4_spec__7___redArg(v_m_945_, v_query_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4_spec__7___boxed(lean_object* v_00_u03b2_948_, lean_object* v_m_949_, lean_object* v_query_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4_spec__7(v_00_u03b2_948_, v_m_949_, v_query_950_);
lean_dec_ref(v_query_950_);
lean_dec_ref(v_m_949_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_952_, lean_object* v_b_953_, lean_object* v_acc_954_, lean_object* v_i_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5_spec__7___redArg(v_b_953_, v_acc_954_, v_i_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b2_957_, lean_object* v_b_958_, lean_object* v_acc_959_, lean_object* v_i_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__5_spec__7(v_00_u03b2_957_, v_b_958_, v_acc_959_, v_i_960_);
lean_dec_ref(v_b_958_);
return v_res_961_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0(void){
_start:
{
lean_object* v_cellCount_962_; lean_object* v___x_963_; 
v_cellCount_962_ = lean_unsigned_to_nat(16u);
v___x_963_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_962_);
return v___x_963_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1(void){
_start:
{
lean_object* v_cellCount_964_; lean_object* v___x_965_; 
v_cellCount_964_ = lean_unsigned_to_nat(16u);
v___x_965_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_964_);
return v___x_965_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__2(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_966_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1);
v___x_967_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0);
v___x_968_ = lean_unsigned_to_nat(0u);
v___x_969_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v___x_967_);
lean_ctor_set(v___x_969_, 2, v___x_966_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(lean_object* v_e_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_976_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__2, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__2_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__2);
v___x_977_ = lean_st_mk_ref(v___x_976_);
v___x_978_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_e_970_, v___x_977_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_987_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_987_ == 0)
{
v___x_981_ = v___x_978_;
v_isShared_982_ = v_isSharedCheck_987_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_978_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_987_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_983_ = lean_st_ref_get(v___x_977_);
lean_dec(v___x_977_);
lean_dec(v___x_983_);
if (v_isShared_982_ == 0)
{
v___x_985_ = v___x_981_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_979_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
else
{
lean_dec(v___x_977_);
return v___x_978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___boxed(lean_object* v_e_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(v_e_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
return v_res_994_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(lean_object* v_m_995_, lean_object* v_a_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4_spec__7___redArg(v_m_995_, v_a_996_);
if (lean_obj_tag(v___x_997_) == 0)
{
uint8_t v___x_998_; 
lean_dec_ref_known(v___x_997_, 3);
v___x_998_ = 1;
return v___x_998_;
}
else
{
uint8_t v___x_999_; 
v___x_999_ = 0;
return v___x_999_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg___boxed(lean_object* v_m_1000_, lean_object* v_a_1001_){
_start:
{
uint8_t v_res_1002_; lean_object* v_r_1003_; 
v_res_1002_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_m_1000_, v_a_1001_);
lean_dec_ref(v_a_1001_);
lean_dec_ref(v_m_1000_);
v_r_1003_ = lean_box(v_res_1002_);
return v_r_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(lean_object* v_e_1009_, uint8_t v_omitTopForall_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v___x_1017_; lean_object* v_seen_1018_; uint8_t v___x_1019_; 
v___x_1017_ = lean_st_ref_get(v_a_1011_);
v_seen_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc_ref(v_seen_1018_);
lean_dec(v___x_1017_);
v___x_1019_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_seen_1018_, v_e_1009_);
lean_dec_ref(v_seen_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1103_; 
lean_inc_ref(v_e_1009_);
v___x_1020_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(v_e_1009_, v_omitTopForall_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_);
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1103_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1103_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; lean_object* v_seen_1026_; lean_object* v_consts_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1102_; 
v___x_1025_ = lean_st_ref_take(v_a_1011_);
v_seen_1026_ = lean_ctor_get(v___x_1025_, 0);
v_consts_1027_ = lean_ctor_get(v___x_1025_, 1);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1029_ = v___x_1025_;
v_isShared_1030_ = v_isSharedCheck_1102_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_consts_1027_);
lean_inc(v_seen_1026_);
lean_dec(v___x_1025_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1102_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___y_1032_; lean_object* v___x_1040_; lean_object* v___y_1042_; lean_object* v_i_1043_; lean_object* v___y_1049_; lean_object* v___y_1059_; lean_object* v_i_1060_; lean_object* v___x_1075_; 
v___x_1040_ = lean_box(0);
v___x_1075_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v_seen_1026_, v_e_1009_);
switch(lean_obj_tag(v___x_1075_))
{
case 0:
{
lean_dec_ref_known(v___x_1075_, 3);
lean_dec_ref(v_e_1009_);
v___y_1032_ = v_seen_1026_;
goto v___jp_1031_;
}
case 1:
{
lean_object* v_index_1076_; lean_object* v_size_1077_; lean_object* v_keyArray_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v_index_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_index_1076_);
lean_dec_ref_known(v___x_1075_, 1);
v_size_1077_ = lean_ctor_get(v_seen_1026_, 0);
v_keyArray_1078_ = lean_ctor_get(v_seen_1026_, 1);
v___x_1079_ = lean_unsigned_to_nat(1u);
v___x_1080_ = lean_nat_add(v_size_1077_, v___x_1079_);
v___x_1081_ = lean_array_get_size(v_keyArray_1078_);
v___x_1082_ = lean_nat_dec_lt(v___x_1080_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_dec(v___x_1080_);
lean_dec(v_index_1076_);
goto v___jp_1065_;
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1083_ = lean_unsigned_to_nat(4u);
v___x_1084_ = lean_nat_mul(v___x_1080_, v___x_1083_);
v___x_1085_ = lean_unsigned_to_nat(3u);
v___x_1086_ = lean_nat_mul(v___x_1081_, v___x_1085_);
v___x_1087_ = lean_nat_dec_le(v___x_1084_, v___x_1086_);
lean_dec(v___x_1086_);
lean_dec(v___x_1084_);
if (v___x_1087_ == 0)
{
lean_dec(v___x_1080_);
lean_dec(v_index_1076_);
goto v___jp_1065_;
}
else
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Std_DHashMap_Raw_setEntry___redArg(v_seen_1026_, v___x_1080_, v_index_1076_, v_e_1009_, v___x_1040_);
lean_dec(v_index_1076_);
v___y_1032_ = v___x_1088_;
goto v___jp_1031_;
}
}
}
default: 
{
lean_object* v_size_1089_; lean_object* v_keyArray_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; 
v_size_1089_ = lean_ctor_get(v_seen_1026_, 0);
v_keyArray_1090_ = lean_ctor_get(v_seen_1026_, 1);
v___x_1091_ = lean_unsigned_to_nat(1u);
v___x_1092_ = lean_nat_add(v_size_1089_, v___x_1091_);
v___x_1093_ = lean_array_get_size(v_keyArray_1090_);
v___x_1094_ = lean_nat_dec_lt(v___x_1092_, v___x_1093_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; 
lean_dec(v___x_1092_);
v___x_1095_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v_seen_1026_);
lean_dec_ref(v_seen_1026_);
v___y_1049_ = v___x_1095_;
goto v___jp_1048_;
}
else
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1096_ = lean_unsigned_to_nat(4u);
v___x_1097_ = lean_nat_mul(v___x_1092_, v___x_1096_);
lean_dec(v___x_1092_);
v___x_1098_ = lean_unsigned_to_nat(3u);
v___x_1099_ = lean_nat_mul(v___x_1093_, v___x_1098_);
v___x_1100_ = lean_nat_dec_le(v___x_1097_, v___x_1099_);
lean_dec(v___x_1099_);
lean_dec(v___x_1097_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v_seen_1026_);
lean_dec_ref(v_seen_1026_);
v___y_1049_ = v___x_1101_;
goto v___jp_1048_;
}
else
{
v___y_1049_ = v_seen_1026_;
goto v___jp_1048_;
}
}
}
}
v___jp_1031_:
{
lean_object* v___x_1034_; 
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___y_1032_);
v___x_1034_ = v___x_1029_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___y_1032_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_consts_1027_);
v___x_1034_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1035_ = lean_st_ref_put(v_a_1011_, v___x_1034_);
if (v_isShared_1024_ == 0)
{
v___x_1037_ = v___x_1023_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1021_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
v___jp_1041_:
{
lean_object* v_size_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v_size_1044_ = lean_ctor_get(v___y_1042_, 0);
v___x_1045_ = lean_unsigned_to_nat(1u);
v___x_1046_ = lean_nat_add(v_size_1044_, v___x_1045_);
v___x_1047_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1042_, v___x_1046_, v_i_1043_, v_e_1009_, v___x_1040_);
lean_dec(v_i_1043_);
v___y_1032_ = v___x_1047_;
goto v___jp_1031_;
}
v___jp_1048_:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v___y_1049_, v_e_1009_);
switch(lean_obj_tag(v___x_1050_))
{
case 0:
{
lean_object* v_index_1051_; lean_object* v_size_1052_; lean_object* v___x_1053_; 
v_index_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_index_1051_);
lean_dec_ref_known(v___x_1050_, 3);
v_size_1052_ = lean_ctor_get(v___y_1049_, 0);
lean_inc(v_size_1052_);
v___x_1053_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1049_, v_size_1052_, v_index_1051_, v_e_1009_, v___x_1040_);
lean_dec(v_index_1051_);
v___y_1032_ = v___x_1053_;
goto v___jp_1031_;
}
case 1:
{
lean_object* v_index_1054_; 
v_index_1054_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_index_1054_);
lean_dec_ref_known(v___x_1050_, 1);
v___y_1042_ = v___y_1049_;
v_i_1043_ = v_index_1054_;
goto v___jp_1041_;
}
default: 
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = lean_unsigned_to_nat(0u);
v___x_1056_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1049_, v___x_1055_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_index_1057_; 
v_index_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_index_1057_);
lean_dec_ref_known(v___x_1056_, 1);
v___y_1042_ = v___y_1049_;
v_i_1043_ = v_index_1057_;
goto v___jp_1041_;
}
else
{
lean_dec_ref(v_e_1009_);
v___y_1032_ = v___y_1049_;
goto v___jp_1031_;
}
}
}
}
v___jp_1058_:
{
lean_object* v_size_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_size_1061_ = lean_ctor_get(v___y_1059_, 0);
v___x_1062_ = lean_unsigned_to_nat(1u);
v___x_1063_ = lean_nat_add(v_size_1061_, v___x_1062_);
v___x_1064_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1059_, v___x_1063_, v_i_1060_, v_e_1009_, v___x_1040_);
lean_dec(v_i_1060_);
v___y_1032_ = v___x_1064_;
goto v___jp_1031_;
}
v___jp_1065_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v_seen_1026_);
lean_dec_ref(v_seen_1026_);
v___x_1067_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v___x_1066_, v_e_1009_);
switch(lean_obj_tag(v___x_1067_))
{
case 0:
{
lean_object* v_index_1068_; lean_object* v_size_1069_; lean_object* v___x_1070_; 
v_index_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_index_1068_);
lean_dec_ref_known(v___x_1067_, 3);
v_size_1069_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_size_1069_);
v___x_1070_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1066_, v_size_1069_, v_index_1068_, v_e_1009_, v___x_1040_);
lean_dec(v_index_1068_);
v___y_1032_ = v___x_1070_;
goto v___jp_1031_;
}
case 1:
{
lean_object* v_index_1071_; 
v_index_1071_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_index_1071_);
lean_dec_ref_known(v___x_1067_, 1);
v___y_1059_ = v___x_1066_;
v_i_1060_ = v_index_1071_;
goto v___jp_1058_;
}
default: 
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_unsigned_to_nat(0u);
v___x_1073_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1066_, v___x_1072_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_index_1074_; 
v_index_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_index_1074_);
lean_dec_ref_known(v___x_1073_, 1);
v___y_1059_ = v___x_1066_;
v_i_1060_ = v_index_1074_;
goto v___jp_1058_;
}
else
{
lean_dec_ref(v_e_1009_);
v___y_1032_ = v___x_1066_;
goto v___jp_1031_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_dec_ref(v_e_1009_);
v___x_1104_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0));
v___x_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
return v___x_1105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(lean_object* v_e_1106_, uint8_t v_omitTopForall_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
switch(lean_obj_tag(v_e_1106_))
{
case 4:
{
lean_object* v_declName_1114_; lean_object* v___x_1115_; lean_object* v_seen_1116_; lean_object* v_consts_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1144_; 
v_declName_1114_ = lean_ctor_get(v_e_1106_, 0);
lean_inc(v_declName_1114_);
lean_dec_ref_known(v_e_1106_, 2);
v___x_1115_ = lean_st_ref_take(v_a_1108_);
v_seen_1116_ = lean_ctor_get(v___x_1115_, 0);
v_consts_1117_ = lean_ctor_get(v___x_1115_, 1);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1119_ = v___x_1115_;
v_isShared_1120_ = v_isSharedCheck_1144_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_consts_1117_);
lean_inc(v_seen_1116_);
lean_dec(v___x_1115_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1144_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; lean_object* v___x_1123_; 
lean_inc(v_declName_1114_);
v___x_1121_ = l_Lean_NameSet_insert(v_consts_1117_, v_declName_1114_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 1, v___x_1121_);
v___x_1123_ = v___x_1119_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_seen_1116_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_st_ref_put(v_a_1108_, v___x_1123_);
v___x_1125_ = l_Lean_Name_eraseMacroScopes(v_declName_1114_);
lean_dec(v_declName_1114_);
if (lean_obj_tag(v___x_1125_) == 1)
{
lean_object* v_str_1126_; lean_object* v___x_1127_; uint32_t v___x_1128_; uint32_t v___x_1129_; uint8_t v___x_1130_; 
v_str_1126_ = lean_ctor_get(v___x_1125_, 1);
lean_inc_ref(v_str_1126_);
lean_dec_ref_known(v___x_1125_, 2);
v___x_1127_ = lean_unsigned_to_nat(0u);
v___x_1128_ = lean_string_utf8_get(v_str_1126_, v___x_1127_);
v___x_1129_ = 97;
v___x_1130_ = lean_uint32_dec_le(v___x_1129_, v___x_1128_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_string_utf8_set(v_str_1126_, v___x_1127_, v___x_1128_);
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
return v___x_1132_;
}
else
{
uint32_t v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = 122;
v___x_1134_ = lean_uint32_dec_le(v___x_1128_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_string_utf8_set(v_str_1126_, v___x_1127_, v___x_1128_);
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
return v___x_1136_;
}
else
{
uint32_t v___x_1137_; uint32_t v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1137_ = 4294967264;
v___x_1138_ = lean_uint32_add(v___x_1128_, v___x_1137_);
v___x_1139_ = lean_string_utf8_set(v_str_1126_, v___x_1127_, v___x_1138_);
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
return v___x_1140_;
}
}
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_dec(v___x_1125_);
v___x_1141_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0));
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
return v___x_1142_;
}
}
}
}
case 5:
{
lean_object* v_fn_1145_; lean_object* v_arg_1146_; uint8_t v___x_1147_; lean_object* v___x_1148_; lean_object* v_a_1149_; lean_object* v___x_1150_; lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1159_; 
v_fn_1145_ = lean_ctor_get(v_e_1106_, 0);
lean_inc_ref(v_fn_1145_);
v_arg_1146_ = lean_ctor_get(v_e_1106_, 1);
lean_inc_ref(v_arg_1146_);
lean_dec_ref_known(v_e_1106_, 2);
v___x_1147_ = 0;
v___x_1148_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_fn_1145_, v___x_1147_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_a_1149_);
lean_dec_ref(v___x_1148_);
v___x_1150_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_arg_1146_, v___x_1147_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1155_ = lean_string_append(v_a_1149_, v_a_1151_);
lean_dec(v_a_1151_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1155_);
v___x_1157_ = v___x_1153_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
case 7:
{
lean_object* v_binderType_1160_; lean_object* v_body_1161_; uint8_t v___x_1162_; lean_object* v___x_1163_; lean_object* v_a_1164_; 
v_binderType_1160_ = lean_ctor_get(v_e_1106_, 1);
lean_inc_ref(v_binderType_1160_);
v_body_1161_ = lean_ctor_get(v_e_1106_, 2);
lean_inc_ref(v_body_1161_);
lean_dec_ref_known(v_e_1106_, 3);
v___x_1162_ = 0;
v___x_1163_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_binderType_1160_, v___x_1162_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_a_1164_);
lean_dec_ref(v___x_1163_);
if (v_omitTopForall_1107_ == 0)
{
goto v___jp_1165_;
}
else
{
lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0));
v___x_1179_ = lean_string_dec_eq(v_a_1164_, v___x_1178_);
if (v___x_1179_ == 0)
{
goto v___jp_1165_;
}
else
{
lean_object* v___x_1180_; 
lean_dec(v_a_1164_);
v___x_1180_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_body_1161_, v_omitTopForall_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
return v___x_1180_;
}
}
v___jp_1165_:
{
lean_object* v___x_1166_; lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1177_; 
v___x_1166_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_body_1161_, v___x_1162_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1169_ = v___x_1166_;
v_isShared_1170_ = v_isSharedCheck_1177_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1177_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1171_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__1));
v___x_1172_ = lean_string_append(v___x_1171_, v_a_1164_);
lean_dec(v_a_1164_);
v___x_1173_ = lean_string_append(v___x_1172_, v_a_1167_);
lean_dec(v_a_1167_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1173_);
v___x_1175_ = v___x_1169_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
case 3:
{
lean_object* v_u_1181_; 
v_u_1181_ = lean_ctor_get(v_e_1106_, 0);
lean_inc(v_u_1181_);
lean_dec_ref_known(v_e_1106_, 1);
switch(lean_obj_tag(v_u_1181_))
{
case 0:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__2));
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
case 1:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec_ref_known(v_u_1181_, 1);
v___x_1184_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__3));
v___x_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
return v___x_1185_;
}
default: 
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
lean_dec(v_u_1181_);
v___x_1186_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__4));
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
return v___x_1187_;
}
}
}
default: 
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec_ref(v_e_1106_);
v___x_1188_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0));
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___boxed(lean_object* v_e_1190_, lean_object* v_omitTopForall_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
uint8_t v_omitTopForall_boxed_1198_; lean_object* v_res_1199_; 
v_omitTopForall_boxed_1198_ = lean_unbox(v_omitTopForall_1191_);
v_res_1199_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(v_e_1190_, v_omitTopForall_boxed_1198_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
lean_dec(v_a_1196_);
lean_dec_ref(v_a_1195_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
lean_dec(v_a_1192_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___boxed(lean_object* v_e_1200_, lean_object* v_omitTopForall_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
uint8_t v_omitTopForall_boxed_1208_; lean_object* v_res_1209_; 
v_omitTopForall_boxed_1208_ = lean_unbox(v_omitTopForall_1201_);
v_res_1209_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_e_1200_, v_omitTopForall_boxed_1208_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
return v_res_1209_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0(lean_object* v_00_u03b2_1210_, lean_object* v_m_1211_, lean_object* v_a_1212_){
_start:
{
uint8_t v___x_1213_; 
v___x_1213_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_m_1211_, v_a_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___boxed(lean_object* v_00_u03b2_1214_, lean_object* v_m_1215_, lean_object* v_a_1216_){
_start:
{
uint8_t v_res_1217_; lean_object* v_r_1218_; 
v_res_1217_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0(v_00_u03b2_1214_, v_m_1215_, v_a_1216_);
lean_dec_ref(v_a_1216_);
lean_dec_ref(v_m_1215_);
v_r_1218_ = lean_box(v_res_1217_);
return v_r_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__3_splitter___redArg(lean_object* v_e_1219_, lean_object* v_h__1_1220_, lean_object* v_h__2_1221_, lean_object* v_h__3_1222_, lean_object* v_h__4_1223_, lean_object* v_h__5_1224_, lean_object* v_h__6_1225_, lean_object* v_h__7_1226_){
_start:
{
switch(lean_obj_tag(v_e_1219_))
{
case 4:
{
lean_object* v_declName_1227_; lean_object* v_us_1228_; lean_object* v___x_1229_; 
lean_dec(v_h__7_1226_);
lean_dec(v_h__6_1225_);
lean_dec(v_h__5_1224_);
lean_dec(v_h__4_1223_);
lean_dec(v_h__3_1222_);
lean_dec(v_h__2_1221_);
v_declName_1227_ = lean_ctor_get(v_e_1219_, 0);
lean_inc(v_declName_1227_);
v_us_1228_ = lean_ctor_get(v_e_1219_, 1);
lean_inc(v_us_1228_);
lean_dec_ref_known(v_e_1219_, 2);
v___x_1229_ = lean_apply_2(v_h__1_1220_, v_declName_1227_, v_us_1228_);
return v___x_1229_;
}
case 5:
{
lean_object* v_fn_1230_; lean_object* v_arg_1231_; lean_object* v___x_1232_; 
lean_dec(v_h__7_1226_);
lean_dec(v_h__6_1225_);
lean_dec(v_h__5_1224_);
lean_dec(v_h__4_1223_);
lean_dec(v_h__3_1222_);
lean_dec(v_h__1_1220_);
v_fn_1230_ = lean_ctor_get(v_e_1219_, 0);
lean_inc_ref(v_fn_1230_);
v_arg_1231_ = lean_ctor_get(v_e_1219_, 1);
lean_inc_ref(v_arg_1231_);
lean_dec_ref_known(v_e_1219_, 2);
v___x_1232_ = lean_apply_2(v_h__2_1221_, v_fn_1230_, v_arg_1231_);
return v___x_1232_;
}
case 7:
{
lean_object* v_binderName_1233_; lean_object* v_binderType_1234_; lean_object* v_body_1235_; uint8_t v_binderInfo_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec(v_h__7_1226_);
lean_dec(v_h__6_1225_);
lean_dec(v_h__5_1224_);
lean_dec(v_h__4_1223_);
lean_dec(v_h__2_1221_);
lean_dec(v_h__1_1220_);
v_binderName_1233_ = lean_ctor_get(v_e_1219_, 0);
lean_inc(v_binderName_1233_);
v_binderType_1234_ = lean_ctor_get(v_e_1219_, 1);
lean_inc_ref(v_binderType_1234_);
v_body_1235_ = lean_ctor_get(v_e_1219_, 2);
lean_inc_ref(v_body_1235_);
v_binderInfo_1236_ = lean_ctor_get_uint8(v_e_1219_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1219_, 3);
v___x_1237_ = lean_box(v_binderInfo_1236_);
v___x_1238_ = lean_apply_4(v_h__3_1222_, v_binderName_1233_, v_binderType_1234_, v_body_1235_, v___x_1237_);
return v___x_1238_;
}
case 3:
{
lean_object* v_u_1239_; 
lean_dec(v_h__7_1226_);
lean_dec(v_h__3_1222_);
lean_dec(v_h__2_1221_);
lean_dec(v_h__1_1220_);
v_u_1239_ = lean_ctor_get(v_e_1219_, 0);
lean_inc(v_u_1239_);
lean_dec_ref_known(v_e_1219_, 1);
switch(lean_obj_tag(v_u_1239_))
{
case 0:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
lean_dec(v_h__6_1225_);
lean_dec(v_h__5_1224_);
v___x_1240_ = lean_box(0);
v___x_1241_ = lean_apply_1(v_h__4_1223_, v___x_1240_);
return v___x_1241_;
}
case 1:
{
lean_object* v_a_1242_; lean_object* v___x_1243_; 
lean_dec(v_h__6_1225_);
lean_dec(v_h__4_1223_);
v_a_1242_ = lean_ctor_get(v_u_1239_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v_u_1239_, 1);
v___x_1243_ = lean_apply_1(v_h__5_1224_, v_a_1242_);
return v___x_1243_;
}
default: 
{
lean_object* v___x_1244_; 
lean_dec(v_h__5_1224_);
lean_dec(v_h__4_1223_);
v___x_1244_ = lean_apply_3(v_h__6_1225_, v_u_1239_, lean_box(0), lean_box(0));
return v___x_1244_;
}
}
}
default: 
{
lean_object* v___x_1245_; 
lean_dec(v_h__6_1225_);
lean_dec(v_h__5_1224_);
lean_dec(v_h__4_1223_);
lean_dec(v_h__3_1222_);
lean_dec(v_h__2_1221_);
lean_dec(v_h__1_1220_);
v___x_1245_ = lean_apply_7(v_h__7_1226_, v_e_1219_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1245_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__3_splitter(lean_object* v_motive_1246_, lean_object* v_e_1247_, lean_object* v_h__1_1248_, lean_object* v_h__2_1249_, lean_object* v_h__3_1250_, lean_object* v_h__4_1251_, lean_object* v_h__5_1252_, lean_object* v_h__6_1253_, lean_object* v_h__7_1254_){
_start:
{
switch(lean_obj_tag(v_e_1247_))
{
case 4:
{
lean_object* v_declName_1255_; lean_object* v_us_1256_; lean_object* v___x_1257_; 
lean_dec(v_h__7_1254_);
lean_dec(v_h__6_1253_);
lean_dec(v_h__5_1252_);
lean_dec(v_h__4_1251_);
lean_dec(v_h__3_1250_);
lean_dec(v_h__2_1249_);
v_declName_1255_ = lean_ctor_get(v_e_1247_, 0);
lean_inc(v_declName_1255_);
v_us_1256_ = lean_ctor_get(v_e_1247_, 1);
lean_inc(v_us_1256_);
lean_dec_ref_known(v_e_1247_, 2);
v___x_1257_ = lean_apply_2(v_h__1_1248_, v_declName_1255_, v_us_1256_);
return v___x_1257_;
}
case 5:
{
lean_object* v_fn_1258_; lean_object* v_arg_1259_; lean_object* v___x_1260_; 
lean_dec(v_h__7_1254_);
lean_dec(v_h__6_1253_);
lean_dec(v_h__5_1252_);
lean_dec(v_h__4_1251_);
lean_dec(v_h__3_1250_);
lean_dec(v_h__1_1248_);
v_fn_1258_ = lean_ctor_get(v_e_1247_, 0);
lean_inc_ref(v_fn_1258_);
v_arg_1259_ = lean_ctor_get(v_e_1247_, 1);
lean_inc_ref(v_arg_1259_);
lean_dec_ref_known(v_e_1247_, 2);
v___x_1260_ = lean_apply_2(v_h__2_1249_, v_fn_1258_, v_arg_1259_);
return v___x_1260_;
}
case 7:
{
lean_object* v_binderName_1261_; lean_object* v_binderType_1262_; lean_object* v_body_1263_; uint8_t v_binderInfo_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_dec(v_h__7_1254_);
lean_dec(v_h__6_1253_);
lean_dec(v_h__5_1252_);
lean_dec(v_h__4_1251_);
lean_dec(v_h__2_1249_);
lean_dec(v_h__1_1248_);
v_binderName_1261_ = lean_ctor_get(v_e_1247_, 0);
lean_inc(v_binderName_1261_);
v_binderType_1262_ = lean_ctor_get(v_e_1247_, 1);
lean_inc_ref(v_binderType_1262_);
v_body_1263_ = lean_ctor_get(v_e_1247_, 2);
lean_inc_ref(v_body_1263_);
v_binderInfo_1264_ = lean_ctor_get_uint8(v_e_1247_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1247_, 3);
v___x_1265_ = lean_box(v_binderInfo_1264_);
v___x_1266_ = lean_apply_4(v_h__3_1250_, v_binderName_1261_, v_binderType_1262_, v_body_1263_, v___x_1265_);
return v___x_1266_;
}
case 3:
{
lean_object* v_u_1267_; 
lean_dec(v_h__7_1254_);
lean_dec(v_h__3_1250_);
lean_dec(v_h__2_1249_);
lean_dec(v_h__1_1248_);
v_u_1267_ = lean_ctor_get(v_e_1247_, 0);
lean_inc(v_u_1267_);
lean_dec_ref_known(v_e_1247_, 1);
switch(lean_obj_tag(v_u_1267_))
{
case 0:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_dec(v_h__6_1253_);
lean_dec(v_h__5_1252_);
v___x_1268_ = lean_box(0);
v___x_1269_ = lean_apply_1(v_h__4_1251_, v___x_1268_);
return v___x_1269_;
}
case 1:
{
lean_object* v_a_1270_; lean_object* v___x_1271_; 
lean_dec(v_h__6_1253_);
lean_dec(v_h__4_1251_);
v_a_1270_ = lean_ctor_get(v_u_1267_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v_u_1267_, 1);
v___x_1271_ = lean_apply_1(v_h__5_1252_, v_a_1270_);
return v___x_1271_;
}
default: 
{
lean_object* v___x_1272_; 
lean_dec(v_h__5_1252_);
lean_dec(v_h__4_1251_);
v___x_1272_ = lean_apply_3(v_h__6_1253_, v_u_1267_, lean_box(0), lean_box(0));
return v___x_1272_;
}
}
}
default: 
{
lean_object* v___x_1273_; 
lean_dec(v_h__6_1253_);
lean_dec(v_h__5_1252_);
lean_dec(v_h__4_1251_);
lean_dec(v_h__3_1250_);
lean_dec(v_h__2_1249_);
lean_dec(v_h__1_1248_);
v___x_1273_ = lean_apply_7(v_h__7_1254_, v_e_1247_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1273_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__1_splitter___redArg(lean_object* v_x_1274_, lean_object* v_h__1_1275_, lean_object* v_h__2_1276_){
_start:
{
if (lean_obj_tag(v_x_1274_) == 1)
{
lean_object* v_pre_1277_; lean_object* v_str_1278_; lean_object* v___x_1279_; 
lean_dec(v_h__2_1276_);
v_pre_1277_ = lean_ctor_get(v_x_1274_, 0);
lean_inc(v_pre_1277_);
v_str_1278_ = lean_ctor_get(v_x_1274_, 1);
lean_inc_ref(v_str_1278_);
lean_dec_ref_known(v_x_1274_, 2);
v___x_1279_ = lean_apply_2(v_h__1_1275_, v_pre_1277_, v_str_1278_);
return v___x_1279_;
}
else
{
lean_object* v___x_1280_; 
lean_dec(v_h__1_1275_);
v___x_1280_ = lean_apply_2(v_h__2_1276_, v_x_1274_, lean_box(0));
return v___x_1280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__1_splitter(lean_object* v_motive_1281_, lean_object* v_x_1282_, lean_object* v_h__1_1283_, lean_object* v_h__2_1284_){
_start:
{
if (lean_obj_tag(v_x_1282_) == 1)
{
lean_object* v_pre_1285_; lean_object* v_str_1286_; lean_object* v___x_1287_; 
lean_dec(v_h__2_1284_);
v_pre_1285_ = lean_ctor_get(v_x_1282_, 0);
lean_inc(v_pre_1285_);
v_str_1286_ = lean_ctor_get(v_x_1282_, 1);
lean_inc_ref(v_str_1286_);
lean_dec_ref_known(v_x_1282_, 2);
v___x_1287_ = lean_apply_2(v_h__1_1283_, v_pre_1285_, v_str_1286_);
return v___x_1287_;
}
else
{
lean_object* v___x_1288_; 
lean_dec(v_h__1_1283_);
v___x_1288_ = lean_apply_2(v_h__2_1284_, v_x_1282_, lean_box(0));
return v___x_1288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore(lean_object* v_e_1289_, uint8_t v_omitTopForall_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_e_1289_, v_omitTopForall_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore___boxed(lean_object* v_e_1298_, lean_object* v_omitTopForall_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
uint8_t v_omitTopForall_boxed_1306_; lean_object* v_res_1307_; 
v_omitTopForall_boxed_1306_ = lean_unbox(v_omitTopForall_1299_);
v_res_1307_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore(v_e_1298_, v_omitTopForall_boxed_1306_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(lean_object* v_e_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
if (lean_obj_tag(v_e_1309_) == 7)
{
lean_object* v_binderType_1316_; lean_object* v_body_1317_; lean_object* v___x_1318_; 
v_binderType_1316_ = lean_ctor_get(v_e_1309_, 1);
lean_inc_ref(v_binderType_1316_);
v_body_1317_ = lean_ctor_get(v_e_1309_, 2);
lean_inc_ref(v_body_1317_);
lean_dec_ref_known(v_e_1309_, 3);
v___x_1318_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(v_body_1317_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v_fst_1320_; lean_object* v_snd_1321_; uint8_t v___x_1322_; lean_object* v___x_1323_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1318_, 1);
v_fst_1320_ = lean_ctor_get(v_a_1319_, 0);
v_snd_1321_ = lean_ctor_get(v_a_1319_, 1);
v___x_1322_ = 1;
v___x_1323_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_binderType_1316_, v___x_1322_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1348_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1326_ = v___x_1323_;
v_isShared_1327_ = v_isSharedCheck_1348_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1323_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1348_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1328_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0));
v___x_1329_ = lean_string_dec_eq(v_a_1324_, v___x_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1342_; 
lean_inc(v_snd_1321_);
lean_inc(v_fst_1320_);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_a_1319_);
if (v_isSharedCheck_1342_ == 0)
{
lean_object* v_unused_1343_; lean_object* v_unused_1344_; 
v_unused_1343_ = lean_ctor_get(v_a_1319_, 1);
lean_dec(v_unused_1343_);
v_unused_1344_ = lean_ctor_get(v_a_1319_, 0);
lean_dec(v_unused_1344_);
v___x_1331_ = v_a_1319_;
v_isShared_1332_ = v_isSharedCheck_1342_;
goto v_resetjp_1330_;
}
else
{
lean_dec(v_a_1319_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1342_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1333_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit___closed__0));
v___x_1334_ = lean_string_append(v___x_1333_, v_a_1324_);
lean_dec(v_a_1324_);
v___x_1335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
lean_ctor_set(v___x_1335_, 1, v_fst_1320_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1335_);
v___x_1337_ = v___x_1331_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1335_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_snd_1321_);
v___x_1337_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1339_; 
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1337_);
v___x_1339_ = v___x_1326_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_object* v___x_1346_; 
lean_dec(v_a_1324_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v_a_1319_);
v___x_1346_ = v___x_1326_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1319_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec(v_a_1319_);
v_a_1349_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1323_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1323_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_1316_);
return v___x_1318_;
}
}
else
{
uint8_t v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = 0;
v___x_1358_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_e_1309_, v___x_1357_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1368_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1361_ = v___x_1358_;
v_isShared_1362_ = v_isSharedCheck_1368_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1358_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1368_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1363_ = lean_box(0);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
lean_ctor_set(v___x_1364_, 1, v_a_1359_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1364_);
v___x_1366_ = v___x_1361_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
v_a_1369_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1358_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1358_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit___boxed(lean_object* v_e_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(v_e_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
lean_dec(v_a_1378_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(lean_object* v_x_1385_, lean_object* v_x_1386_){
_start:
{
if (lean_obj_tag(v_x_1386_) == 0)
{
return v_x_1385_;
}
else
{
lean_object* v_head_1387_; lean_object* v_tail_1388_; lean_object* v___x_1389_; 
v_head_1387_ = lean_ctor_get(v_x_1386_, 0);
v_tail_1388_ = lean_ctor_get(v_x_1386_, 1);
v___x_1389_ = lean_string_append(v_x_1385_, v_head_1387_);
v_x_1385_ = v___x_1389_;
v_x_1386_ = v_tail_1388_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0___boxed(lean_object* v_x_1391_, lean_object* v_x_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(v_x_1391_, v_x_1392_);
lean_dec(v_x_1392_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(lean_object* v_e_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(v_e_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1414_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1414_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1414_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v_fst_1406_; lean_object* v_snd_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
v_fst_1406_ = lean_ctor_get(v_a_1402_, 0);
lean_inc(v_fst_1406_);
v_snd_1407_ = lean_ctor_get(v_a_1402_, 1);
lean_inc(v_snd_1407_);
lean_dec(v_a_1402_);
v___x_1408_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0));
v___x_1409_ = l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(v___x_1408_, v_fst_1406_);
lean_dec(v_fst_1406_);
v___x_1410_ = lean_string_append(v_snd_1407_, v___x_1409_);
lean_dec_ref(v___x_1409_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1410_);
v___x_1412_ = v___x_1404_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
v_a_1415_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1401_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1401_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux___boxed(lean_object* v_e_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(v_e_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
lean_dec(v_a_1428_);
lean_dec_ref(v_a_1427_);
lean_dec(v_a_1426_);
lean_dec_ref(v_a_1425_);
lean_dec(v_a_1424_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(lean_object* v_ns_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_){
_start:
{
switch(lean_obj_tag(v_ns_1431_))
{
case 0:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = lean_box(0);
v___x_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
return v___x_1436_;
}
case 1:
{
lean_object* v_pre_1437_; lean_object* v___x_1438_; lean_object* v_env_1439_; uint8_t v___x_1440_; uint8_t v___x_1441_; 
v_pre_1437_ = lean_ctor_get(v_ns_1431_, 0);
lean_inc(v_pre_1437_);
v___x_1438_ = lean_st_ref_get(v_a_1433_);
v_env_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc_ref(v_env_1439_);
lean_dec(v___x_1438_);
v___x_1440_ = 1;
lean_inc_ref(v_ns_1431_);
v___x_1441_ = l_Lean_Environment_contains(v_env_1439_, v_ns_1431_, v___x_1440_);
if (v___x_1441_ == 0)
{
lean_dec_ref_known(v_ns_1431_, 2);
v_ns_1431_ = v_pre_1437_;
goto _start;
}
else
{
lean_object* v___x_1443_; lean_object* v_seen_1444_; lean_object* v_consts_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1521_; 
v___x_1443_ = lean_st_ref_take(v_a_1432_);
v_seen_1444_ = lean_ctor_get(v___x_1443_, 0);
v_consts_1445_ = lean_ctor_get(v___x_1443_, 1);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1447_ = v___x_1443_;
v_isShared_1448_ = v_isSharedCheck_1521_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_consts_1445_);
lean_inc(v_seen_1444_);
lean_dec(v___x_1443_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1521_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___y_1450_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___y_1461_; lean_object* v_i_1462_; lean_object* v___y_1468_; lean_object* v___y_1478_; lean_object* v_i_1479_; lean_object* v___x_1494_; 
v___x_1457_ = lean_box(0);
lean_inc_ref(v_ns_1431_);
v___x_1458_ = l_Lean_Expr_const___override(v_ns_1431_, v___x_1457_);
v___x_1459_ = lean_box(0);
v___x_1494_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v_seen_1444_, v___x_1458_);
switch(lean_obj_tag(v___x_1494_))
{
case 0:
{
lean_dec_ref_known(v___x_1494_, 3);
lean_dec_ref(v___x_1458_);
v___y_1450_ = v_seen_1444_;
goto v___jp_1449_;
}
case 1:
{
lean_object* v_index_1495_; lean_object* v_size_1496_; lean_object* v_keyArray_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; 
v_index_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_index_1495_);
lean_dec_ref_known(v___x_1494_, 1);
v_size_1496_ = lean_ctor_get(v_seen_1444_, 0);
v_keyArray_1497_ = lean_ctor_get(v_seen_1444_, 1);
v___x_1498_ = lean_unsigned_to_nat(1u);
v___x_1499_ = lean_nat_add(v_size_1496_, v___x_1498_);
v___x_1500_ = lean_array_get_size(v_keyArray_1497_);
v___x_1501_ = lean_nat_dec_lt(v___x_1499_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_dec(v___x_1499_);
lean_dec(v_index_1495_);
goto v___jp_1484_;
}
else
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1502_ = lean_unsigned_to_nat(4u);
v___x_1503_ = lean_nat_mul(v___x_1499_, v___x_1502_);
v___x_1504_ = lean_unsigned_to_nat(3u);
v___x_1505_ = lean_nat_mul(v___x_1500_, v___x_1504_);
v___x_1506_ = lean_nat_dec_le(v___x_1503_, v___x_1505_);
lean_dec(v___x_1505_);
lean_dec(v___x_1503_);
if (v___x_1506_ == 0)
{
lean_dec(v___x_1499_);
lean_dec(v_index_1495_);
goto v___jp_1484_;
}
else
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Std_DHashMap_Raw_setEntry___redArg(v_seen_1444_, v___x_1499_, v_index_1495_, v___x_1458_, v___x_1459_);
lean_dec(v_index_1495_);
v___y_1450_ = v___x_1507_;
goto v___jp_1449_;
}
}
}
default: 
{
lean_object* v_size_1508_; lean_object* v_keyArray_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; 
v_size_1508_ = lean_ctor_get(v_seen_1444_, 0);
v_keyArray_1509_ = lean_ctor_get(v_seen_1444_, 1);
v___x_1510_ = lean_unsigned_to_nat(1u);
v___x_1511_ = lean_nat_add(v_size_1508_, v___x_1510_);
v___x_1512_ = lean_array_get_size(v_keyArray_1509_);
v___x_1513_ = lean_nat_dec_lt(v___x_1511_, v___x_1512_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; 
lean_dec(v___x_1511_);
v___x_1514_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v_seen_1444_);
lean_dec_ref(v_seen_1444_);
v___y_1468_ = v___x_1514_;
goto v___jp_1467_;
}
else
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
v___x_1515_ = lean_unsigned_to_nat(4u);
v___x_1516_ = lean_nat_mul(v___x_1511_, v___x_1515_);
lean_dec(v___x_1511_);
v___x_1517_ = lean_unsigned_to_nat(3u);
v___x_1518_ = lean_nat_mul(v___x_1512_, v___x_1517_);
v___x_1519_ = lean_nat_dec_le(v___x_1516_, v___x_1518_);
lean_dec(v___x_1518_);
lean_dec(v___x_1516_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v_seen_1444_);
lean_dec_ref(v_seen_1444_);
v___y_1468_ = v___x_1520_;
goto v___jp_1467_;
}
else
{
v___y_1468_ = v_seen_1444_;
goto v___jp_1467_;
}
}
}
}
v___jp_1449_:
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1451_ = l_Lean_NameSet_insert(v_consts_1445_, v_ns_1431_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 1, v___x_1451_);
lean_ctor_set(v___x_1447_, 0, v___y_1450_);
v___x_1453_ = v___x_1447_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___y_1450_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_st_ref_put(v_a_1432_, v___x_1453_);
v_ns_1431_ = v_pre_1437_;
goto _start;
}
}
v___jp_1460_:
{
lean_object* v_size_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v_size_1463_ = lean_ctor_get(v___y_1461_, 0);
v___x_1464_ = lean_unsigned_to_nat(1u);
v___x_1465_ = lean_nat_add(v_size_1463_, v___x_1464_);
v___x_1466_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1461_, v___x_1465_, v_i_1462_, v___x_1458_, v___x_1459_);
lean_dec(v_i_1462_);
v___y_1450_ = v___x_1466_;
goto v___jp_1449_;
}
v___jp_1467_:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v___y_1468_, v___x_1458_);
switch(lean_obj_tag(v___x_1469_))
{
case 0:
{
lean_object* v_index_1470_; lean_object* v_size_1471_; lean_object* v___x_1472_; 
v_index_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_index_1470_);
lean_dec_ref_known(v___x_1469_, 3);
v_size_1471_ = lean_ctor_get(v___y_1468_, 0);
lean_inc(v_size_1471_);
v___x_1472_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1468_, v_size_1471_, v_index_1470_, v___x_1458_, v___x_1459_);
lean_dec(v_index_1470_);
v___y_1450_ = v___x_1472_;
goto v___jp_1449_;
}
case 1:
{
lean_object* v_index_1473_; 
v_index_1473_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_index_1473_);
lean_dec_ref_known(v___x_1469_, 1);
v___y_1461_ = v___y_1468_;
v_i_1462_ = v_index_1473_;
goto v___jp_1460_;
}
default: 
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = lean_unsigned_to_nat(0u);
v___x_1475_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1468_, v___x_1474_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_index_1476_; 
v_index_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_index_1476_);
lean_dec_ref_known(v___x_1475_, 1);
v___y_1461_ = v___y_1468_;
v_i_1462_ = v_index_1476_;
goto v___jp_1460_;
}
else
{
lean_dec_ref(v___x_1458_);
v___y_1450_ = v___y_1468_;
goto v___jp_1449_;
}
}
}
}
v___jp_1477_:
{
lean_object* v_size_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v_size_1480_ = lean_ctor_get(v___y_1478_, 0);
v___x_1481_ = lean_unsigned_to_nat(1u);
v___x_1482_ = lean_nat_add(v_size_1480_, v___x_1481_);
v___x_1483_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1478_, v___x_1482_, v_i_1479_, v___x_1458_, v___x_1459_);
lean_dec(v_i_1479_);
v___y_1450_ = v___x_1483_;
goto v___jp_1449_;
}
v___jp_1484_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v_seen_1444_);
lean_dec_ref(v_seen_1444_);
v___x_1486_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v___x_1485_, v___x_1458_);
switch(lean_obj_tag(v___x_1486_))
{
case 0:
{
lean_object* v_index_1487_; lean_object* v_size_1488_; lean_object* v___x_1489_; 
v_index_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_index_1487_);
lean_dec_ref_known(v___x_1486_, 3);
v_size_1488_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_size_1488_);
v___x_1489_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1485_, v_size_1488_, v_index_1487_, v___x_1458_, v___x_1459_);
lean_dec(v_index_1487_);
v___y_1450_ = v___x_1489_;
goto v___jp_1449_;
}
case 1:
{
lean_object* v_index_1490_; 
v_index_1490_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_index_1490_);
lean_dec_ref_known(v___x_1486_, 1);
v___y_1478_ = v___x_1485_;
v_i_1479_ = v_index_1490_;
goto v___jp_1477_;
}
default: 
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = lean_unsigned_to_nat(0u);
v___x_1492_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1485_, v___x_1491_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_index_1493_; 
v_index_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_index_1493_);
lean_dec_ref_known(v___x_1492_, 1);
v___y_1478_ = v___x_1485_;
v_i_1479_ = v_index_1493_;
goto v___jp_1477_;
}
else
{
lean_dec_ref(v___x_1458_);
v___y_1450_ = v___x_1485_;
goto v___jp_1449_;
}
}
}
}
}
}
}
default: 
{
lean_object* v_pre_1522_; 
v_pre_1522_ = lean_ctor_get(v_ns_1431_, 0);
lean_inc(v_pre_1522_);
lean_dec_ref_known(v_ns_1431_, 2);
v_ns_1431_ = v_pre_1522_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg___boxed(lean_object* v_ns_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(v_ns_1524_, v_a_1525_, v_a_1526_);
lean_dec(v_a_1526_);
lean_dec(v_a_1525_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace(lean_object* v_ns_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(v_ns_1529_, v_a_1530_, v_a_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___boxed(lean_object* v_ns_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace(v_ns_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
lean_dec(v_a_1542_);
lean_dec_ref(v_a_1541_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
lean_dec(v_a_1538_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(lean_object* v_e_1545_, lean_object* v___y_1546_){
_start:
{
uint8_t v___x_1548_; 
v___x_1548_ = l_Lean_Expr_hasMVar(v_e_1545_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1549_, 0, v_e_1545_);
return v___x_1549_;
}
else
{
lean_object* v___x_1550_; lean_object* v_mctx_1551_; lean_object* v___x_1552_; lean_object* v_fst_1553_; lean_object* v_snd_1554_; lean_object* v___x_1555_; lean_object* v_cache_1556_; lean_object* v_zetaDeltaFVarIds_1557_; lean_object* v_postponed_1558_; lean_object* v_diag_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1568_; 
v___x_1550_ = lean_st_ref_get(v___y_1546_);
v_mctx_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc_ref(v_mctx_1551_);
lean_dec(v___x_1550_);
v___x_1552_ = l_Lean_instantiateMVarsCore(v_mctx_1551_, v_e_1545_);
v_fst_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_fst_1553_);
v_snd_1554_ = lean_ctor_get(v___x_1552_, 1);
lean_inc(v_snd_1554_);
lean_dec_ref(v___x_1552_);
v___x_1555_ = lean_st_ref_take(v___y_1546_);
v_cache_1556_ = lean_ctor_get(v___x_1555_, 1);
v_zetaDeltaFVarIds_1557_ = lean_ctor_get(v___x_1555_, 2);
v_postponed_1558_ = lean_ctor_get(v___x_1555_, 3);
v_diag_1559_ = lean_ctor_get(v___x_1555_, 4);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; 
v_unused_1569_ = lean_ctor_get(v___x_1555_, 0);
lean_dec(v_unused_1569_);
v___x_1561_ = v___x_1555_;
v_isShared_1562_ = v_isSharedCheck_1568_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_diag_1559_);
lean_inc(v_postponed_1558_);
lean_inc(v_zetaDeltaFVarIds_1557_);
lean_inc(v_cache_1556_);
lean_dec(v___x_1555_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1568_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v_snd_1554_);
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_snd_1554_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_cache_1556_);
lean_ctor_set(v_reuseFailAlloc_1567_, 2, v_zetaDeltaFVarIds_1557_);
lean_ctor_set(v_reuseFailAlloc_1567_, 3, v_postponed_1558_);
lean_ctor_set(v_reuseFailAlloc_1567_, 4, v_diag_1559_);
v___x_1564_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_st_ref_put(v___y_1546_, v___x_1564_);
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v_fst_1553_);
return v___x_1566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg___boxed(lean_object* v_e_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_1570_, v___y_1571_);
lean_dec(v___y_1571_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0(lean_object* v_e_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_1574_, v___y_1577_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___boxed(lean_object* v_e_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0(v_e_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(lean_object* v_e_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v___x_1597_; lean_object* v_a_1598_; lean_object* v_currNamespace_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1597_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_1590_, v_a_1593_);
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1598_);
lean_dec_ref(v___x_1597_);
v_currNamespace_1599_ = lean_ctor_get(v_a_1594_, 6);
lean_inc(v_currNamespace_1599_);
v___x_1600_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(v_currNamespace_1599_, v_a_1591_, v_a_1595_);
lean_dec_ref(v___x_1600_);
v___x_1601_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(v_a_1598_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1603_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1601_, 1);
v___x_1603_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(v_a_1602_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
return v___x_1603_;
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
v_a_1604_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1601_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1601_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName___boxed(lean_object* v_e_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(v_e_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_);
lean_dec(v_a_1617_);
lean_dec_ref(v_a_1616_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
lean_dec(v_a_1613_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(lean_object* v_x_1621_){
_start:
{
switch(lean_obj_tag(v_x_1621_))
{
case 0:
{
lean_object* v___x_1622_; 
v___x_1622_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0));
return v___x_1622_;
}
case 1:
{
lean_object* v_pre_1623_; lean_object* v_str_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; uint32_t v___x_1629_; uint32_t v___x_1630_; uint8_t v___x_1631_; 
v_pre_1623_ = lean_ctor_get(v_x_1621_, 0);
lean_inc(v_pre_1623_);
v_str_1624_ = lean_ctor_get(v_x_1621_, 1);
lean_inc_ref(v_str_1624_);
lean_dec_ref_known(v_x_1621_, 2);
v___x_1625_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(v_pre_1623_);
v___x_1626_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix___closed__0));
v___x_1627_ = lean_string_append(v___x_1625_, v___x_1626_);
v___x_1628_ = lean_unsigned_to_nat(0u);
v___x_1629_ = lean_string_utf8_get(v_str_1624_, v___x_1628_);
v___x_1630_ = 65;
v___x_1631_ = lean_uint32_dec_le(v___x_1630_, v___x_1629_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = lean_string_utf8_set(v_str_1624_, v___x_1628_, v___x_1629_);
v___x_1633_ = lean_string_append(v___x_1627_, v___x_1632_);
lean_dec_ref(v___x_1632_);
return v___x_1633_;
}
else
{
uint32_t v___x_1634_; uint8_t v___x_1635_; 
v___x_1634_ = 90;
v___x_1635_ = lean_uint32_dec_le(v___x_1629_, v___x_1634_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = lean_string_utf8_set(v_str_1624_, v___x_1628_, v___x_1629_);
v___x_1637_ = lean_string_append(v___x_1627_, v___x_1636_);
lean_dec_ref(v___x_1636_);
return v___x_1637_;
}
else
{
uint32_t v___x_1638_; uint32_t v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1638_ = 32;
v___x_1639_ = lean_uint32_add(v___x_1629_, v___x_1638_);
v___x_1640_ = lean_string_utf8_set(v_str_1624_, v___x_1628_, v___x_1639_);
v___x_1641_ = lean_string_append(v___x_1627_, v___x_1640_);
lean_dec_ref(v___x_1640_);
return v___x_1641_;
}
}
}
default: 
{
lean_object* v_pre_1642_; 
v_pre_1642_ = lean_ctor_get(v_x_1621_, 0);
lean_inc(v_pre_1642_);
lean_dec_ref_known(v_x_1621_, 2);
v_x_1621_ = v_pre_1642_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(lean_object* v___y_1644_){
_start:
{
lean_object* v___x_1646_; lean_object* v_env_1647_; lean_object* v___x_1648_; lean_object* v_mainModule_1649_; lean_object* v___x_1650_; 
v___x_1646_ = lean_st_ref_get(v___y_1644_);
v_env_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc_ref(v_env_1647_);
lean_dec(v___x_1646_);
v___x_1648_ = l_Lean_Environment_header(v_env_1647_);
lean_dec_ref(v_env_1647_);
v_mainModule_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_mainModule_1649_);
lean_dec_ref(v___x_1648_);
v___x_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1650_, 0, v_mainModule_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg___boxed(lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v___y_1651_);
lean_dec(v___y_1651_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1(lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v___y_1657_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___boxed(lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1(v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
return v_res_1665_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(lean_object* v_x_1666_, lean_object* v_x_1667_){
_start:
{
if (lean_obj_tag(v_x_1666_) == 0)
{
if (lean_obj_tag(v_x_1667_) == 0)
{
uint8_t v___x_1668_; 
v___x_1668_ = 1;
return v___x_1668_;
}
else
{
uint8_t v___x_1669_; 
v___x_1669_ = 0;
return v___x_1669_;
}
}
else
{
if (lean_obj_tag(v_x_1667_) == 0)
{
uint8_t v___x_1670_; 
v___x_1670_ = 0;
return v___x_1670_;
}
else
{
lean_object* v_val_1671_; lean_object* v_val_1672_; uint8_t v___x_1673_; 
v_val_1671_ = lean_ctor_get(v_x_1666_, 0);
v_val_1672_ = lean_ctor_get(v_x_1667_, 0);
v___x_1673_ = lean_name_eq(v_val_1671_, v_val_1672_);
return v___x_1673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2___boxed(lean_object* v_x_1674_, lean_object* v_x_1675_){
_start:
{
uint8_t v_res_1676_; lean_object* v_r_1677_; 
v_res_1676_ = l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(v_x_1674_, v_x_1675_);
lean_dec(v_x_1675_);
lean_dec(v_x_1674_);
v_r_1677_ = lean_box(v_res_1676_);
return v_r_1677_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0(lean_object* v_e_1678_){
_start:
{
if (lean_obj_tag(v_e_1678_) == 4)
{
lean_object* v_declName_1679_; uint8_t v___x_1680_; 
v_declName_1679_ = lean_ctor_get(v_e_1678_, 0);
v___x_1680_ = l_Lean_Name_hasMacroScopes(v_declName_1679_);
return v___x_1680_;
}
else
{
uint8_t v___x_1681_; 
v___x_1681_ = 0;
return v___x_1681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0___boxed(lean_object* v_e_1682_){
_start:
{
uint8_t v_res_1683_; lean_object* v_r_1684_; 
v_res_1683_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0(v_e_1682_);
lean_dec_ref(v_e_1682_);
v_r_1684_ = lean_box(v_res_1683_);
return v_r_1684_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(lean_object* v_as_1685_, size_t v_i_1686_, size_t v_stop_1687_){
_start:
{
uint8_t v___x_1688_; 
v___x_1688_ = lean_usize_dec_eq(v_i_1686_, v_stop_1687_);
if (v___x_1688_ == 0)
{
uint8_t v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = 1;
v___x_1690_ = lean_array_uget_borrowed(v_as_1685_, v_i_1686_);
if (lean_obj_tag(v___x_1690_) == 0)
{
return v___x_1689_;
}
else
{
if (v___x_1688_ == 0)
{
size_t v___x_1691_; size_t v___x_1692_; 
v___x_1691_ = ((size_t)1ULL);
v___x_1692_ = lean_usize_add(v_i_1686_, v___x_1691_);
v_i_1686_ = v___x_1692_;
goto _start;
}
else
{
return v___x_1689_;
}
}
}
else
{
uint8_t v___x_1694_; 
v___x_1694_ = 0;
return v___x_1694_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5___boxed(lean_object* v_as_1695_, lean_object* v_i_1696_, lean_object* v_stop_1697_){
_start:
{
size_t v_i_boxed_1698_; size_t v_stop_boxed_1699_; uint8_t v_res_1700_; lean_object* v_r_1701_; 
v_i_boxed_1698_ = lean_unbox_usize(v_i_1696_);
lean_dec(v_i_1696_);
v_stop_boxed_1699_ = lean_unbox_usize(v_stop_1697_);
lean_dec(v_stop_1697_);
v_res_1700_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(v_as_1695_, v_i_boxed_1698_, v_stop_boxed_1699_);
lean_dec_ref(v_as_1695_);
v_r_1701_ = lean_box(v_res_1700_);
return v_r_1701_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(lean_object* v___x_1702_, lean_object* v_as_1703_, size_t v_i_1704_, size_t v_stop_1705_){
_start:
{
uint8_t v___x_1706_; 
v___x_1706_ = lean_usize_dec_eq(v_i_1704_, v_stop_1705_);
if (v___x_1706_ == 0)
{
uint8_t v___x_1707_; lean_object* v___y_1709_; lean_object* v___x_1715_; 
v___x_1707_ = 1;
v___x_1715_ = lean_array_uget(v_as_1703_, v_i_1704_);
if (lean_obj_tag(v___x_1715_) == 0)
{
v___y_1709_ = v___x_1715_;
goto v___jp_1708_;
}
else
{
lean_object* v_val_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1724_; 
v_val_1716_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1718_ = v___x_1715_;
v_isShared_1719_ = v_isSharedCheck_1724_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_val_1716_);
lean_dec(v___x_1715_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1724_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1720_ = l_Lean_Name_getRoot(v_val_1716_);
lean_dec(v_val_1716_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1720_);
v___x_1722_ = v___x_1718_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
v___y_1709_ = v___x_1722_;
goto v___jp_1708_;
}
}
}
v___jp_1708_:
{
lean_object* v___x_1710_; uint8_t v___x_1711_; 
lean_inc(v___x_1702_);
v___x_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1702_);
v___x_1711_ = l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(v___y_1709_, v___x_1710_);
lean_dec_ref_known(v___x_1710_, 1);
lean_dec(v___y_1709_);
if (v___x_1711_ == 0)
{
size_t v___x_1712_; size_t v___x_1713_; 
v___x_1712_ = ((size_t)1ULL);
v___x_1713_ = lean_usize_add(v_i_1704_, v___x_1712_);
v_i_1704_ = v___x_1713_;
goto _start;
}
else
{
lean_dec(v___x_1702_);
return v___x_1707_;
}
}
}
else
{
uint8_t v___x_1725_; 
lean_dec(v___x_1702_);
v___x_1725_ = 0;
return v___x_1725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4___boxed(lean_object* v___x_1726_, lean_object* v_as_1727_, lean_object* v_i_1728_, lean_object* v_stop_1729_){
_start:
{
size_t v_i_boxed_1730_; size_t v_stop_boxed_1731_; uint8_t v_res_1732_; lean_object* v_r_1733_; 
v_i_boxed_1730_ = lean_unbox_usize(v_i_1728_);
lean_dec(v_i_1728_);
v_stop_boxed_1731_ = lean_unbox_usize(v_stop_1729_);
lean_dec(v_stop_1729_);
v_res_1732_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(v___x_1726_, v_as_1727_, v_i_boxed_1730_, v_stop_boxed_1731_);
lean_dec_ref(v_as_1727_);
v_r_1733_ = lean_box(v_res_1732_);
return v_r_1733_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1734_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
return v___x_1736_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1737_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_1738_ = lean_unsigned_to_nat(0u);
v___x_1739_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
lean_ctor_set(v___x_1739_, 2, v___x_1738_);
lean_ctor_set(v___x_1739_, 3, v___x_1738_);
lean_ctor_set(v___x_1739_, 4, v___x_1737_);
lean_ctor_set(v___x_1739_, 5, v___x_1737_);
lean_ctor_set(v___x_1739_, 6, v___x_1737_);
lean_ctor_set(v___x_1739_, 7, v___x_1737_);
lean_ctor_set(v___x_1739_, 8, v___x_1737_);
lean_ctor_set(v___x_1739_, 9, v___x_1737_);
lean_ctor_set(v___x_1739_, 10, v___x_1737_);
return v___x_1739_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1740_ = lean_unsigned_to_nat(32u);
v___x_1741_ = lean_mk_empty_array_with_capacity(v___x_1740_);
v___x_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
return v___x_1742_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1743_ = ((size_t)5ULL);
v___x_1744_ = lean_unsigned_to_nat(0u);
v___x_1745_ = lean_unsigned_to_nat(32u);
v___x_1746_ = lean_mk_empty_array_with_capacity(v___x_1745_);
v___x_1747_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_1748_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
lean_ctor_set(v___x_1748_, 1, v___x_1746_);
lean_ctor_set(v___x_1748_, 2, v___x_1744_);
lean_ctor_set(v___x_1748_, 3, v___x_1744_);
lean_ctor_set_usize(v___x_1748_, 4, v___x_1743_);
return v___x_1748_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1749_ = lean_box(1);
v___x_1750_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_1751_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_1752_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
lean_ctor_set(v___x_1752_, 1, v___x_1750_);
lean_ctor_set(v___x_1752_, 2, v___x_1749_);
return v___x_1752_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_1755_ = l_Lean_stringToMessageData(v___x_1754_);
return v___x_1755_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_1758_ = l_Lean_stringToMessageData(v___x_1757_);
return v___x_1758_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_1761_ = l_Lean_stringToMessageData(v___x_1760_);
return v___x_1761_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_1764_ = l_Lean_stringToMessageData(v___x_1763_);
return v___x_1764_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__14));
v___x_1767_ = l_Lean_stringToMessageData(v___x_1766_);
return v___x_1767_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__16));
v___x_1770_ = l_Lean_stringToMessageData(v___x_1769_);
return v___x_1770_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__18));
v___x_1773_ = l_Lean_stringToMessageData(v___x_1772_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_1774_, lean_object* v_declHint_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v___x_1778_; lean_object* v_env_1779_; uint8_t v___x_1780_; 
v___x_1778_ = lean_st_ref_get(v___y_1776_);
v_env_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc_ref(v_env_1779_);
lean_dec(v___x_1778_);
v___x_1780_ = l_Lean_Name_isAnonymous(v_declHint_1775_);
if (v___x_1780_ == 0)
{
uint8_t v_isExporting_1781_; 
v_isExporting_1781_ = lean_ctor_get_uint8(v_env_1779_, sizeof(void*)*8);
if (v_isExporting_1781_ == 0)
{
lean_object* v___x_1782_; 
lean_dec_ref(v_env_1779_);
lean_dec(v_declHint_1775_);
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v_msg_1774_);
return v___x_1782_;
}
else
{
lean_object* v___x_1783_; uint8_t v___x_1784_; 
lean_inc_ref(v_env_1779_);
v___x_1783_ = l_Lean_Environment_setExporting(v_env_1779_, v___x_1780_);
lean_inc(v_declHint_1775_);
lean_inc_ref(v___x_1783_);
v___x_1784_ = l_Lean_Environment_contains(v___x_1783_, v_declHint_1775_, v_isExporting_1781_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; 
lean_dec_ref(v___x_1783_);
lean_dec_ref(v_env_1779_);
lean_dec(v_declHint_1775_);
v___x_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1785_, 0, v_msg_1774_);
return v___x_1785_;
}
else
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v_c_1791_; lean_object* v___x_1792_; 
v___x_1786_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_1787_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5);
v___x_1788_ = l_Lean_Options_empty;
v___x_1789_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1783_);
lean_ctor_set(v___x_1789_, 1, v___x_1786_);
lean_ctor_set(v___x_1789_, 2, v___x_1787_);
lean_ctor_set(v___x_1789_, 3, v___x_1788_);
lean_inc(v_declHint_1775_);
v___x_1790_ = l_Lean_MessageData_ofConstName(v_declHint_1775_, v___x_1780_);
v_c_1791_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1791_, 0, v___x_1789_);
lean_ctor_set(v_c_1791_, 1, v___x_1790_);
v___x_1792_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1779_, v_declHint_1775_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
lean_dec_ref(v_env_1779_);
lean_dec(v_declHint_1775_);
v___x_1793_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_1794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
lean_ctor_set(v___x_1794_, 1, v_c_1791_);
v___x_1795_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9);
v___x_1796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1794_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
v___x_1797_ = l_Lean_MessageData_note(v___x_1796_);
v___x_1798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1798_, 0, v_msg_1774_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
v___x_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
return v___x_1799_;
}
else
{
lean_object* v_val_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1835_; 
v_val_1800_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1802_ = v___x_1792_;
v_isShared_1803_ = v_isSharedCheck_1835_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_val_1800_);
lean_dec(v___x_1792_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1835_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v_mod_1807_; uint8_t v___x_1808_; 
v___x_1804_ = lean_box(0);
v___x_1805_ = l_Lean_Environment_header(v_env_1779_);
lean_dec_ref(v_env_1779_);
v___x_1806_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1805_);
v_mod_1807_ = lean_array_get(v___x_1804_, v___x_1806_, v_val_1800_);
lean_dec(v_val_1800_);
lean_dec_ref(v___x_1806_);
v___x_1808_ = l_Lean_isPrivateName(v_declHint_1775_);
lean_dec(v_declHint_1775_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1820_; 
v___x_1809_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_1810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
lean_ctor_set(v___x_1810_, 1, v_c_1791_);
v___x_1811_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_1812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = l_Lean_MessageData_ofName(v_mod_1807_);
v___x_1814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1812_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_1816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1814_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = l_Lean_MessageData_note(v___x_1816_);
v___x_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1818_, 0, v_msg_1774_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set_tag(v___x_1802_, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1818_);
v___x_1820_ = v___x_1802_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
else
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1822_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_1823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
lean_ctor_set(v___x_1823_, 1, v_c_1791_);
v___x_1824_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1823_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = l_Lean_MessageData_ofName(v_mod_1807_);
v___x_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1825_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19);
v___x_1829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1827_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = l_Lean_MessageData_note(v___x_1829_);
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v_msg_1774_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set_tag(v___x_1802_, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1831_);
v___x_1833_ = v___x_1802_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1836_; 
lean_dec_ref(v_env_1779_);
lean_dec(v_declHint_1775_);
v___x_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1836_, 0, v_msg_1774_);
return v___x_1836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_1837_, lean_object* v_declHint_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_1837_, v_declHint_1838_, v___y_1839_);
lean_dec(v___y_1839_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(lean_object* v_msg_1842_, lean_object* v_declHint_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v___x_1849_; lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1859_; 
v___x_1849_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_1842_, v_declHint_1843_, v___y_1847_);
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1852_ = v___x_1849_;
v_isShared_1853_ = v_isSharedCheck_1859_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1859_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1854_ = l_Lean_unknownIdentifierMessageTag;
v___x_1855_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
lean_ctor_set(v___x_1855_, 1, v_a_1850_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v___x_1855_);
v___x_1857_ = v___x_1852_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1860_, lean_object* v_declHint_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(v_msg_1860_, v_declHint_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(lean_object* v_ref_1868_, lean_object* v_msg_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_fileName_1875_; lean_object* v_fileMap_1876_; lean_object* v_options_1877_; lean_object* v_currRecDepth_1878_; lean_object* v_maxRecDepth_1879_; lean_object* v_ref_1880_; lean_object* v_currNamespace_1881_; lean_object* v_openDecls_1882_; lean_object* v_initHeartbeats_1883_; lean_object* v_maxHeartbeats_1884_; lean_object* v_quotContext_1885_; lean_object* v_currMacroScope_1886_; uint8_t v_diag_1887_; lean_object* v_cancelTk_x3f_1888_; uint8_t v_suppressElabErrors_1889_; lean_object* v_inheritedTraceOptions_1890_; lean_object* v_ref_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v_fileName_1875_ = lean_ctor_get(v___y_1872_, 0);
v_fileMap_1876_ = lean_ctor_get(v___y_1872_, 1);
v_options_1877_ = lean_ctor_get(v___y_1872_, 2);
v_currRecDepth_1878_ = lean_ctor_get(v___y_1872_, 3);
v_maxRecDepth_1879_ = lean_ctor_get(v___y_1872_, 4);
v_ref_1880_ = lean_ctor_get(v___y_1872_, 5);
v_currNamespace_1881_ = lean_ctor_get(v___y_1872_, 6);
v_openDecls_1882_ = lean_ctor_get(v___y_1872_, 7);
v_initHeartbeats_1883_ = lean_ctor_get(v___y_1872_, 8);
v_maxHeartbeats_1884_ = lean_ctor_get(v___y_1872_, 9);
v_quotContext_1885_ = lean_ctor_get(v___y_1872_, 10);
v_currMacroScope_1886_ = lean_ctor_get(v___y_1872_, 11);
v_diag_1887_ = lean_ctor_get_uint8(v___y_1872_, sizeof(void*)*14);
v_cancelTk_x3f_1888_ = lean_ctor_get(v___y_1872_, 12);
v_suppressElabErrors_1889_ = lean_ctor_get_uint8(v___y_1872_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1890_ = lean_ctor_get(v___y_1872_, 13);
v_ref_1891_ = l_Lean_replaceRef(v_ref_1868_, v_ref_1880_);
lean_inc_ref(v_inheritedTraceOptions_1890_);
lean_inc(v_cancelTk_x3f_1888_);
lean_inc(v_currMacroScope_1886_);
lean_inc(v_quotContext_1885_);
lean_inc(v_maxHeartbeats_1884_);
lean_inc(v_initHeartbeats_1883_);
lean_inc(v_openDecls_1882_);
lean_inc(v_currNamespace_1881_);
lean_inc(v_maxRecDepth_1879_);
lean_inc(v_currRecDepth_1878_);
lean_inc_ref(v_options_1877_);
lean_inc_ref(v_fileMap_1876_);
lean_inc_ref(v_fileName_1875_);
v___x_1892_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1892_, 0, v_fileName_1875_);
lean_ctor_set(v___x_1892_, 1, v_fileMap_1876_);
lean_ctor_set(v___x_1892_, 2, v_options_1877_);
lean_ctor_set(v___x_1892_, 3, v_currRecDepth_1878_);
lean_ctor_set(v___x_1892_, 4, v_maxRecDepth_1879_);
lean_ctor_set(v___x_1892_, 5, v_ref_1891_);
lean_ctor_set(v___x_1892_, 6, v_currNamespace_1881_);
lean_ctor_set(v___x_1892_, 7, v_openDecls_1882_);
lean_ctor_set(v___x_1892_, 8, v_initHeartbeats_1883_);
lean_ctor_set(v___x_1892_, 9, v_maxHeartbeats_1884_);
lean_ctor_set(v___x_1892_, 10, v_quotContext_1885_);
lean_ctor_set(v___x_1892_, 11, v_currMacroScope_1886_);
lean_ctor_set(v___x_1892_, 12, v_cancelTk_x3f_1888_);
lean_ctor_set(v___x_1892_, 13, v_inheritedTraceOptions_1890_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14, v_diag_1887_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 1, v_suppressElabErrors_1889_);
v___x_1893_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v_msg_1869_, v___y_1870_, v___y_1871_, v___x_1892_, v___y_1873_);
lean_dec_ref_known(v___x_1892_, 14);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_ref_1894_, lean_object* v_msg_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_1894_, v_msg_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v_ref_1894_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(lean_object* v_ref_1902_, lean_object* v_msg_1903_, lean_object* v_declHint_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v___x_1910_; lean_object* v_a_1911_; lean_object* v___x_1912_; 
v___x_1910_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(v_msg_1903_, v_declHint_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
lean_dec_ref(v___x_1910_);
v___x_1912_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_1902_, v_a_1911_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg___boxed(lean_object* v_ref_1913_, lean_object* v_msg_1914_, lean_object* v_declHint_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_1913_, v_msg_1914_, v_declHint_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v_ref_1913_);
return v_res_1921_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__0));
v___x_1924_ = l_Lean_stringToMessageData(v___x_1923_);
return v___x_1924_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__2));
v___x_1927_ = l_Lean_stringToMessageData(v___x_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_ref_1928_, lean_object* v_constName_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v___x_1935_; uint8_t v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1935_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1);
v___x_1936_ = 0;
lean_inc(v_constName_1929_);
v___x_1937_ = l_Lean_MessageData_ofConstName(v_constName_1929_, v___x_1936_);
v___x_1938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1935_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3);
v___x_1940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1938_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_1928_, v___x_1940_, v_constName_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v_ref_1942_, lean_object* v_constName_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1942_, v_constName_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v_ref_1942_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(lean_object* v_constName_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_ref_1956_; lean_object* v___x_1957_; 
v_ref_1956_ = lean_ctor_get(v___y_1953_, 5);
v___x_1957_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1956_, v_constName_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_constName_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(lean_object* v_constName_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v___x_1971_; lean_object* v_env_1972_; uint8_t v___x_1973_; lean_object* v___x_1974_; 
v___x_1971_ = lean_st_ref_get(v___y_1969_);
v_env_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc_ref(v_env_1972_);
lean_dec(v___x_1971_);
v___x_1973_ = 0;
lean_inc(v_constName_1965_);
v___x_1974_ = l_Lean_Environment_find_x3f(v_env_1972_, v_constName_1965_, v___x_1973_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
return v___x_1975_;
}
else
{
lean_object* v_val_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
lean_dec(v_constName_1965_);
v_val_1976_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1978_ = v___x_1974_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_val_1976_);
lean_dec(v___x_1974_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set_tag(v___x_1978_, 0);
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_val_1976_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0___boxed(lean_object* v_constName_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(v_constName_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(lean_object* v_declName_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v___x_1997_; 
lean_inc(v_declName_1991_);
v___x_1997_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(v_declName_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2024_; 
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; 
v_unused_2025_ = lean_ctor_get(v___x_1997_, 0);
lean_dec(v_unused_2025_);
v___x_1999_ = v___x_1997_;
v_isShared_2000_ = v_isSharedCheck_2024_;
goto v_resetjp_1998_;
}
else
{
lean_dec(v___x_1997_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2024_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2001_; lean_object* v_env_2002_; lean_object* v___x_2003_; 
v___x_2001_ = lean_st_ref_get(v___y_1995_);
v_env_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc_ref(v_env_2002_);
lean_dec(v___x_2001_);
v___x_2003_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2002_, v_declName_1991_);
lean_dec(v_declName_1991_);
lean_dec_ref(v_env_2002_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v___x_2004_; lean_object* v___x_2006_; 
v___x_2004_ = lean_box(0);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 0, v___x_2004_);
v___x_2006_ = v___x_1999_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
else
{
lean_object* v_val_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2023_; 
v_val_2008_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2010_ = v___x_2003_;
v_isShared_2011_ = v_isSharedCheck_2023_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_val_2008_);
lean_dec(v___x_2003_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2023_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; lean_object* v_env_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2012_ = lean_st_ref_get(v___y_1995_);
v_env_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc_ref(v_env_2013_);
lean_dec(v___x_2012_);
v___x_2014_ = lean_box(0);
v___x_2015_ = l_Lean_Environment_allImportedModuleNames(v_env_2013_);
lean_dec_ref(v_env_2013_);
v___x_2016_ = lean_array_get(v___x_2014_, v___x_2015_, v_val_2008_);
lean_dec(v_val_2008_);
lean_dec_ref(v___x_2015_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2016_);
v___x_2018_ = v___x_2010_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
lean_object* v___x_2020_; 
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 0, v___x_2018_);
v___x_2020_ = v___x_1999_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec(v_declName_1991_);
v_a_2026_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_1997_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_1997_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0___boxed(lean_object* v_declName_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(v_declName_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(lean_object* v_init_2041_, lean_object* v_x_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
if (lean_obj_tag(v_x_2042_) == 0)
{
lean_object* v_k_2048_; lean_object* v_l_2049_; lean_object* v_r_2050_; lean_object* v___x_2051_; 
v_k_2048_ = lean_ctor_get(v_x_2042_, 1);
lean_inc(v_k_2048_);
v_l_2049_ = lean_ctor_get(v_x_2042_, 3);
lean_inc(v_l_2049_);
v_r_2050_ = lean_ctor_get(v_x_2042_, 4);
lean_inc(v_r_2050_);
lean_dec_ref_known(v_x_2042_, 5);
v___x_2051_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v_init_2041_, v_l_2049_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2053_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2051_, 1);
v___x_2053_ = l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(v_k_2048_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2055_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref_known(v___x_2053_, 1);
v___x_2055_ = lean_array_push(v_a_2052_, v_a_2054_);
v_init_2041_ = v___x_2055_;
v_x_2042_ = v_r_2050_;
goto _start;
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec(v_a_2052_);
lean_dec(v_r_2050_);
v_a_2057_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2053_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2053_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
lean_dec(v_r_2050_);
lean_dec(v_k_2048_);
return v___x_2051_;
}
}
else
{
lean_object* v___x_2065_; 
v___x_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2065_, 0, v_init_2041_);
return v___x_2065_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3___boxed(lean_object* v_init_2066_, lean_object* v_x_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v_init_2066_, v_x_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
return v_res_2073_;
}
}
static lean_object* _init_l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0(void){
_start:
{
lean_object* v_cellCount_2074_; lean_object* v___x_2075_; 
v_cellCount_2074_ = lean_unsigned_to_nat(16u);
v___x_2075_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2074_);
return v___x_2075_;
}
}
static lean_object* _init_l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2076_ = lean_obj_once(&l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0, &l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0_once, _init_l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0);
v___x_2077_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0);
v___x_2078_ = lean_unsigned_to_nat(0u);
v___x_2079_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
lean_ctor_set(v___x_2079_, 1, v___x_2077_);
lean_ctor_set(v___x_2079_, 2, v___x_2076_);
return v___x_2079_;
}
}
static lean_object* _init_l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__2(void){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2080_ = l_Lean_NameSet_empty;
v___x_2081_ = lean_obj_once(&l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1, &l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1_once, _init_l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1);
v___x_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
lean_ctor_set(v___x_2082_, 1, v___x_2080_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(lean_object* v_pre_2084_, lean_object* v_type_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2091_ = lean_unsigned_to_nat(0u);
v___x_2092_ = lean_obj_once(&l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__2, &l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__2_once, _init_l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__2);
v___x_2093_ = lean_st_mk_ref(v___x_2092_);
lean_inc_ref(v_type_2085_);
v___x_2094_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(v_type_2085_, v___x_2093_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2144_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2096_ = lean_st_ref_get(v___x_2093_);
lean_dec(v___x_2093_);
v___x_2097_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v_a_2089_);
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2100_ = v___x_2097_;
v_isShared_2101_ = v_isSharedCheck_2144_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2097_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2144_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v_consts_2102_; lean_object* v___f_2103_; lean_object* v___y_2105_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2126_; 
v_consts_2102_ = lean_ctor_get(v___x_2096_, 1);
lean_inc(v_consts_2102_);
lean_dec(v___x_2096_);
v___f_2103_ = ((lean_object*)(l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__3));
v___x_2113_ = lean_string_append(v_pre_2084_, v_a_2095_);
lean_dec(v_a_2095_);
v___x_2114_ = l_Lean_Name_getRoot(v_a_2098_);
lean_dec(v_a_2098_);
if (lean_obj_tag(v_consts_2102_) == 0)
{
lean_object* v_size_2143_; 
v_size_2143_ = lean_ctor_get(v_consts_2102_, 0);
lean_inc(v_size_2143_);
v___y_2126_ = v_size_2143_;
goto v___jp_2125_;
}
else
{
v___y_2126_ = v___x_2091_;
goto v___jp_2125_;
}
v___jp_2104_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2106_ = lean_box(0);
v___x_2107_ = l_Lean_Name_str___override(v___x_2106_, v___y_2105_);
v___x_2108_ = lean_find_expr(v___f_2103_, v_type_2085_);
lean_dec_ref(v_type_2085_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v___x_2110_; 
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 0, v___x_2107_);
v___x_2110_ = v___x_2100_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2107_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
else
{
lean_object* v___x_2112_; 
lean_dec_ref_known(v___x_2108_, 1);
lean_del_object(v___x_2100_);
v___x_2112_ = l_Lean_Core_mkFreshUserName(v___x_2107_, v_a_2088_, v_a_2089_);
return v___x_2112_;
}
}
v___jp_2115_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(v___x_2114_);
v___x_2117_ = lean_string_append(v___x_2113_, v___x_2116_);
lean_dec_ref(v___x_2116_);
v___y_2105_ = v___x_2117_;
goto v___jp_2104_;
}
v___jp_2118_:
{
uint8_t v___x_2121_; 
v___x_2121_ = lean_nat_dec_lt(v___x_2091_, v___y_2119_);
if (v___x_2121_ == 0)
{
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
goto v___jp_2115_;
}
else
{
if (v___x_2121_ == 0)
{
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
goto v___jp_2115_;
}
else
{
size_t v___x_2122_; size_t v___x_2123_; uint8_t v___x_2124_; 
v___x_2122_ = ((size_t)0ULL);
v___x_2123_ = lean_usize_of_nat(v___y_2119_);
lean_dec(v___y_2119_);
lean_inc(v___x_2114_);
v___x_2124_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(v___x_2114_, v___y_2120_, v___x_2122_, v___x_2123_);
lean_dec_ref(v___y_2120_);
if (v___x_2124_ == 0)
{
goto v___jp_2115_;
}
else
{
lean_dec(v___x_2114_);
v___y_2105_ = v___x_2113_;
goto v___jp_2104_;
}
}
}
}
v___jp_2125_:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = lean_mk_empty_array_with_capacity(v___y_2126_);
lean_dec(v___y_2126_);
v___x_2128_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v___x_2127_, v_consts_2102_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v___x_2128_, 1);
v___x_2130_ = lean_array_get_size(v_a_2129_);
v___x_2131_ = lean_nat_dec_lt(v___x_2091_, v___x_2130_);
if (v___x_2131_ == 0)
{
v___y_2119_ = v___x_2130_;
v___y_2120_ = v_a_2129_;
goto v___jp_2118_;
}
else
{
if (v___x_2131_ == 0)
{
v___y_2119_ = v___x_2130_;
v___y_2120_ = v_a_2129_;
goto v___jp_2118_;
}
else
{
size_t v___x_2132_; size_t v___x_2133_; uint8_t v___x_2134_; 
v___x_2132_ = ((size_t)0ULL);
v___x_2133_ = lean_usize_of_nat(v___x_2130_);
v___x_2134_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(v_a_2129_, v___x_2132_, v___x_2133_);
if (v___x_2134_ == 0)
{
v___y_2119_ = v___x_2130_;
v___y_2120_ = v_a_2129_;
goto v___jp_2118_;
}
else
{
lean_dec(v_a_2129_);
lean_dec(v___x_2114_);
v___y_2105_ = v___x_2113_;
goto v___jp_2104_;
}
}
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec(v___x_2114_);
lean_dec_ref(v___x_2113_);
lean_del_object(v___x_2100_);
lean_dec_ref(v_type_2085_);
v_a_2135_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2128_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2128_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec(v___x_2093_);
lean_dec_ref(v_type_2085_);
lean_dec_ref(v_pre_2084_);
v_a_2145_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2094_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2094_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___boxed(lean_object* v_pre_2153_, lean_object* v_type_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(v_pre_2153_, v_type_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
lean_dec(v_a_2156_);
lean_dec_ref(v_a_2155_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_2161_, lean_object* v_constName_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v___x_2168_; 
v___x_2168_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_2169_, lean_object* v_constName_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3(v_00_u03b1_2169_, v_constName_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b1_2177_, lean_object* v_ref_2178_, lean_object* v_constName_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_2178_, v_constName_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_00_u03b1_2186_, lean_object* v_ref_2187_, lean_object* v_constName_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7(v_00_u03b1_2186_, v_ref_2187_, v_constName_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v_ref_2187_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8(lean_object* v_00_u03b1_2195_, lean_object* v_ref_2196_, lean_object* v_msg_2197_, lean_object* v_declHint_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_2196_, v_msg_2197_, v_declHint_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___boxed(lean_object* v_00_u03b1_2205_, lean_object* v_ref_2206_, lean_object* v_msg_2207_, lean_object* v_declHint_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8(v_00_u03b1_2205_, v_ref_2206_, v_msg_2207_, v_declHint_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v_ref_2206_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10(lean_object* v_msg_2215_, lean_object* v_declHint_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_2215_, v_declHint_2216_, v___y_2220_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_2223_, lean_object* v_declHint_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10(v_msg_2223_, v_declHint_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_2231_, lean_object* v_ref_2232_, lean_object* v_msg_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_2232_, v_msg_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_2240_, lean_object* v_ref_2241_, lean_object* v_msg_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10(v_00_u03b1_2240_, v_ref_2241_, v_msg_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v_ref_2241_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg(lean_object* v_a_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg___boxed(lean_object* v_a_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg(v_a_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0(lean_object* v_00_u03b1_2267_, lean_object* v_a_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v___x_2276_; 
v___x_2276_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___boxed(lean_object* v_00_u03b1_2277_, lean_object* v_a_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0(v_00_u03b1_2277_, v_a_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0(lean_object* v_type_2287_, lean_object* v_binds_2288_, lean_object* v_pre_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Lean_Elab_Term_elabType(v_type_2287_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; uint8_t v___x_2299_; uint8_t v___x_2300_; uint8_t v___x_2301_; lean_object* v___x_2302_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___x_2297_, 1);
v___x_2299_ = 0;
v___x_2300_ = 1;
v___x_2301_ = 1;
v___x_2302_ = l_Lean_Meta_mkForallFVars(v_binds_2288_, v_a_2298_, v___x_2299_, v___x_2300_, v___x_2300_, v___x_2301_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2304_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2302_, 1);
v___x_2304_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(v_pre_2289_, v_a_2303_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
return v___x_2304_;
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec_ref(v_pre_2289_);
v_a_2305_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2302_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2302_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_dec_ref(v_pre_2289_);
v_a_2313_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2297_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2297_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0___boxed(lean_object* v_type_2321_, lean_object* v_binds_2322_, lean_object* v_pre_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0(v_type_2321_, v_binds_2322_, v_pre_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec_ref(v_binds_2322_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1(lean_object* v_type_2332_, lean_object* v_pre_2333_, lean_object* v_binds_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___f_2342_; lean_object* v___x_2343_; 
v___f_2342_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2342_, 0, v_type_2332_);
lean_closure_set(v___f_2342_, 1, v_binds_2334_);
lean_closure_set(v___f_2342_, 2, v_pre_2333_);
v___x_2343_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_2342_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1___boxed(lean_object* v_type_2344_, lean_object* v_pre_2345_, lean_object* v_binds_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1(v_type_2344_, v_pre_2345_, v_binds_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3(lean_object* v_currNamespace_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2358_, 0, v_currNamespace_2355_);
lean_ctor_set(v___x_2358_, 1, v___y_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3___boxed(lean_object* v_currNamespace_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3(v_currNamespace_2359_, v___y_2360_, v___y_2361_);
lean_dec_ref(v___y_2360_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(lean_object* v_x_2363_, lean_object* v___y_2364_){
_start:
{
if (lean_obj_tag(v_x_2363_) == 0)
{
lean_object* v_a_2365_; lean_object* v___x_2366_; 
v_a_2365_ = lean_ctor_get(v_x_2363_, 0);
lean_inc(v_a_2365_);
v___x_2366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2366_, 0, v_a_2365_);
lean_ctor_set(v___x_2366_, 1, v___y_2364_);
return v___x_2366_;
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2368_; 
v_a_2367_ = lean_ctor_get(v_x_2363_, 0);
lean_inc(v_a_2367_);
v___x_2368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2368_, 0, v_a_2367_);
lean_ctor_set(v___x_2368_, 1, v___y_2364_);
return v___x_2368_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg___boxed(lean_object* v_x_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v_x_2369_, v___y_2370_);
lean_dec_ref(v_x_2369_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0(lean_object* v_env_2372_, lean_object* v_stx_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2372_, v_stx_2373_, v___y_2374_, v___y_2375_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2377_);
if (lean_obj_tag(v_a_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2386_; 
v_a_2378_ = lean_ctor_get(v___x_2376_, 1);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2386_ == 0)
{
lean_object* v_unused_2387_; 
v_unused_2387_ = lean_ctor_get(v___x_2376_, 0);
lean_dec(v_unused_2387_);
v___x_2380_ = v___x_2376_;
v_isShared_2381_ = v_isSharedCheck_2386_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2376_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2386_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2382_; lean_object* v___x_2384_; 
v___x_2382_ = lean_box(0);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v___x_2382_);
v___x_2384_ = v___x_2380_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_a_2378_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
else
{
lean_object* v_val_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2416_; 
v_val_2388_ = lean_ctor_get(v_a_2377_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v_a_2377_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2390_ = v_a_2377_;
v_isShared_2391_ = v_isSharedCheck_2416_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_val_2388_);
lean_dec(v_a_2377_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2416_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v_snd_2392_; 
v_snd_2392_ = lean_ctor_get(v_val_2388_, 1);
lean_inc(v_snd_2392_);
lean_dec(v_val_2388_);
if (lean_obj_tag(v_snd_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2402_; 
lean_del_object(v___x_2390_);
v_a_2393_ = lean_ctor_get(v___x_2376_, 1);
lean_inc(v_a_2393_);
lean_dec_ref_known(v___x_2376_, 2);
v_a_2394_ = lean_ctor_get(v_snd_2392_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v_snd_2392_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2396_ = v_snd_2392_;
v_isShared_2397_ = v_isSharedCheck_2402_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v_snd_2392_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2402_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v___x_2399_, v_a_2393_);
lean_dec_ref(v___x_2399_);
return v___x_2400_;
}
}
}
else
{
lean_object* v_a_2403_; lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2415_; 
v_a_2403_ = lean_ctor_get(v___x_2376_, 1);
lean_inc(v_a_2403_);
lean_dec_ref_known(v___x_2376_, 2);
v_a_2404_ = lean_ctor_get(v_snd_2392_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v_snd_2392_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2406_ = v_snd_2392_;
v_isShared_2407_ = v_isSharedCheck_2415_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v_snd_2392_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2415_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v_a_2404_);
v___x_2409_ = v___x_2390_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v___x_2411_; 
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 0, v___x_2409_);
v___x_2411_ = v___x_2406_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v___x_2411_, v_a_2403_);
lean_dec_ref(v___x_2411_);
return v___x_2412_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2417_; lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
v_a_2417_ = lean_ctor_get(v___x_2376_, 0);
v_a_2418_ = lean_ctor_get(v___x_2376_, 1);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2376_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_inc(v_a_2417_);
lean_dec(v___x_2376_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2417_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0___boxed(lean_object* v_env_2426_, lean_object* v_stx_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0(v_env_2426_, v_stx_2427_, v___y_2428_, v___y_2429_);
lean_dec_ref(v___y_2428_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1(lean_object* v_env_2431_, lean_object* v_declName_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
uint8_t v___x_2435_; lean_object* v_env_2436_; lean_object* v___x_2437_; uint8_t v___x_2438_; uint8_t v___x_2439_; 
v___x_2435_ = 0;
v_env_2436_ = l_Lean_Environment_setExporting(v_env_2431_, v___x_2435_);
lean_inc(v_declName_2432_);
v___x_2437_ = l_Lean_mkPrivateName(v_env_2436_, v_declName_2432_);
v___x_2438_ = 1;
lean_inc_ref(v_env_2436_);
v___x_2439_ = l_Lean_Environment_contains(v_env_2436_, v___x_2437_, v___x_2438_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2440_; uint8_t v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2440_ = l_Lean_privateToUserName(v_declName_2432_);
v___x_2441_ = l_Lean_Environment_contains(v_env_2436_, v___x_2440_, v___x_2438_);
v___x_2442_ = lean_box(v___x_2441_);
v___x_2443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
lean_ctor_set(v___x_2443_, 1, v___y_2434_);
return v___x_2443_;
}
else
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
lean_dec_ref(v_env_2436_);
lean_dec(v_declName_2432_);
v___x_2444_ = lean_box(v___x_2439_);
v___x_2445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
lean_ctor_set(v___x_2445_, 1, v___y_2434_);
return v___x_2445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1___boxed(lean_object* v_env_2446_, lean_object* v_declName_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1(v_env_2446_, v_declName_2447_, v___y_2448_, v___y_2449_);
lean_dec_ref(v___y_2448_);
return v_res_2450_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__0(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = lean_box(1);
v___x_2452_ = l_Lean_MessageData_ofFormat(v___x_2451_);
return v___x_2452_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__3(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__2));
v___x_2457_ = l_Lean_MessageData_ofFormat(v___x_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19(lean_object* v_x_2458_, lean_object* v_x_2459_){
_start:
{
if (lean_obj_tag(v_x_2459_) == 0)
{
return v_x_2458_;
}
else
{
lean_object* v_head_2460_; lean_object* v_tail_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2483_; 
v_head_2460_ = lean_ctor_get(v_x_2459_, 0);
v_tail_2461_ = lean_ctor_get(v_x_2459_, 1);
v_isSharedCheck_2483_ = !lean_is_exclusive(v_x_2459_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2463_ = v_x_2459_;
v_isShared_2464_ = v_isSharedCheck_2483_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_tail_2461_);
lean_inc(v_head_2460_);
lean_dec(v_x_2459_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2483_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v_before_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2481_; 
v_before_2465_ = lean_ctor_get(v_head_2460_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v_head_2460_);
if (v_isSharedCheck_2481_ == 0)
{
lean_object* v_unused_2482_; 
v_unused_2482_ = lean_ctor_get(v_head_2460_, 1);
lean_dec(v_unused_2482_);
v___x_2467_ = v_head_2460_;
v_isShared_2468_ = v_isSharedCheck_2481_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_before_2465_);
lean_dec(v_head_2460_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2481_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2469_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__0);
if (v_isShared_2468_ == 0)
{
lean_ctor_set_tag(v___x_2467_, 7);
lean_ctor_set(v___x_2467_, 1, v___x_2469_);
lean_ctor_set(v___x_2467_, 0, v_x_2458_);
v___x_2471_ = v___x_2467_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_x_2458_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2472_; lean_object* v___x_2474_; 
v___x_2472_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__3);
if (v_isShared_2464_ == 0)
{
lean_ctor_set_tag(v___x_2463_, 7);
lean_ctor_set(v___x_2463_, 1, v___x_2472_);
lean_ctor_set(v___x_2463_, 0, v___x_2471_);
v___x_2474_ = v___x_2463_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2475_ = l_Lean_MessageData_ofSyntax(v_before_2465_);
v___x_2476_ = l_Lean_indentD(v___x_2475_);
v___x_2477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2474_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
v_x_2458_ = v___x_2477_;
v_x_2459_ = v_tail_2461_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18(lean_object* v_opts_2484_, lean_object* v_opt_2485_){
_start:
{
lean_object* v_name_2486_; lean_object* v_defValue_2487_; lean_object* v_map_2488_; lean_object* v___x_2489_; 
v_name_2486_ = lean_ctor_get(v_opt_2485_, 0);
v_defValue_2487_ = lean_ctor_get(v_opt_2485_, 1);
v_map_2488_ = lean_ctor_get(v_opts_2484_, 0);
v___x_2489_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2488_, v_name_2486_);
if (lean_obj_tag(v___x_2489_) == 0)
{
uint8_t v___x_2490_; 
v___x_2490_ = lean_unbox(v_defValue_2487_);
return v___x_2490_;
}
else
{
lean_object* v_val_2491_; 
v_val_2491_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_val_2491_);
lean_dec_ref_known(v___x_2489_, 1);
if (lean_obj_tag(v_val_2491_) == 1)
{
uint8_t v_v_2492_; 
v_v_2492_ = lean_ctor_get_uint8(v_val_2491_, 0);
lean_dec_ref_known(v_val_2491_, 0);
return v_v_2492_;
}
else
{
uint8_t v___x_2493_; 
lean_dec(v_val_2491_);
v___x_2493_ = lean_unbox(v_defValue_2487_);
return v___x_2493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___boxed(lean_object* v_opts_2494_, lean_object* v_opt_2495_){
_start:
{
uint8_t v_res_2496_; lean_object* v_r_2497_; 
v_res_2496_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18(v_opts_2494_, v_opt_2495_);
lean_dec_ref(v_opt_2495_);
lean_dec_ref(v_opts_2494_);
v_r_2497_ = lean_box(v_res_2496_);
return v_r_2497_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2(void){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__1));
v___x_2502_ = l_Lean_MessageData_ofFormat(v___x_2501_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(lean_object* v_msgData_2503_, lean_object* v_macroStack_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_options_2507_; lean_object* v___x_2508_; uint8_t v___x_2509_; 
v_options_2507_ = lean_ctor_get(v___y_2505_, 2);
v___x_2508_ = l_Lean_Elab_pp_macroStack;
v___x_2509_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18(v_options_2507_, v___x_2508_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; 
lean_dec(v_macroStack_2504_);
v___x_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2510_, 0, v_msgData_2503_);
return v___x_2510_;
}
else
{
if (lean_obj_tag(v_macroStack_2504_) == 0)
{
lean_object* v___x_2511_; 
v___x_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2511_, 0, v_msgData_2503_);
return v___x_2511_;
}
else
{
lean_object* v_head_2512_; lean_object* v_after_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2528_; 
v_head_2512_ = lean_ctor_get(v_macroStack_2504_, 0);
lean_inc(v_head_2512_);
v_after_2513_ = lean_ctor_get(v_head_2512_, 1);
v_isSharedCheck_2528_ = !lean_is_exclusive(v_head_2512_);
if (v_isSharedCheck_2528_ == 0)
{
lean_object* v_unused_2529_; 
v_unused_2529_ = lean_ctor_get(v_head_2512_, 0);
lean_dec(v_unused_2529_);
v___x_2515_ = v_head_2512_;
v_isShared_2516_ = v_isSharedCheck_2528_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_after_2513_);
lean_dec(v_head_2512_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2528_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2517_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19___closed__0);
if (v_isShared_2516_ == 0)
{
lean_ctor_set_tag(v___x_2515_, 7);
lean_ctor_set(v___x_2515_, 1, v___x_2517_);
lean_ctor_set(v___x_2515_, 0, v_msgData_2503_);
v___x_2519_ = v___x_2515_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_msgData_2503_);
lean_ctor_set(v_reuseFailAlloc_2527_, 1, v___x_2517_);
v___x_2519_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v_msgData_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2520_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2);
v___x_2521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2519_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
v___x_2522_ = l_Lean_MessageData_ofSyntax(v_after_2513_);
v___x_2523_ = l_Lean_indentD(v___x_2522_);
v_msgData_2524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2524_, 0, v___x_2521_);
lean_ctor_set(v_msgData_2524_, 1, v___x_2523_);
v___x_2525_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__19(v_msgData_2524_, v_macroStack_2504_);
v___x_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
return v___x_2526_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___boxed(lean_object* v_msgData_2530_, lean_object* v_macroStack_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_msgData_2530_, v_macroStack_2531_, v___y_2532_);
lean_dec_ref(v___y_2532_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(lean_object* v_msg_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v_ref_2543_; lean_object* v___x_2544_; lean_object* v_a_2545_; lean_object* v_macroStack_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2557_; 
v_ref_2543_ = lean_ctor_get(v___y_2540_, 5);
v___x_2544_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msg_2535_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref(v___x_2544_);
v_macroStack_2546_ = lean_ctor_get(v___y_2536_, 1);
v___x_2547_ = l_Lean_Elab_getBetterRef(v_ref_2543_, v_macroStack_2546_);
lean_inc(v_macroStack_2546_);
v___x_2548_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_a_2545_, v_macroStack_2546_, v___y_2540_);
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2551_ = v___x_2548_;
v_isShared_2552_ = v_isSharedCheck_2557_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2548_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2557_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2553_; lean_object* v___x_2555_; 
v___x_2553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2547_);
lean_ctor_set(v___x_2553_, 1, v_a_2549_);
if (v_isShared_2552_ == 0)
{
lean_ctor_set_tag(v___x_2551_, 1);
lean_ctor_set(v___x_2551_, 0, v___x_2553_);
v___x_2555_ = v___x_2551_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2553_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg___boxed(lean_object* v_msg_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(lean_object* v_ref_2567_, lean_object* v_msg_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_fileName_2576_; lean_object* v_fileMap_2577_; lean_object* v_options_2578_; lean_object* v_currRecDepth_2579_; lean_object* v_maxRecDepth_2580_; lean_object* v_ref_2581_; lean_object* v_currNamespace_2582_; lean_object* v_openDecls_2583_; lean_object* v_initHeartbeats_2584_; lean_object* v_maxHeartbeats_2585_; lean_object* v_quotContext_2586_; lean_object* v_currMacroScope_2587_; uint8_t v_diag_2588_; lean_object* v_cancelTk_x3f_2589_; uint8_t v_suppressElabErrors_2590_; lean_object* v_inheritedTraceOptions_2591_; lean_object* v_ref_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v_fileName_2576_ = lean_ctor_get(v___y_2573_, 0);
v_fileMap_2577_ = lean_ctor_get(v___y_2573_, 1);
v_options_2578_ = lean_ctor_get(v___y_2573_, 2);
v_currRecDepth_2579_ = lean_ctor_get(v___y_2573_, 3);
v_maxRecDepth_2580_ = lean_ctor_get(v___y_2573_, 4);
v_ref_2581_ = lean_ctor_get(v___y_2573_, 5);
v_currNamespace_2582_ = lean_ctor_get(v___y_2573_, 6);
v_openDecls_2583_ = lean_ctor_get(v___y_2573_, 7);
v_initHeartbeats_2584_ = lean_ctor_get(v___y_2573_, 8);
v_maxHeartbeats_2585_ = lean_ctor_get(v___y_2573_, 9);
v_quotContext_2586_ = lean_ctor_get(v___y_2573_, 10);
v_currMacroScope_2587_ = lean_ctor_get(v___y_2573_, 11);
v_diag_2588_ = lean_ctor_get_uint8(v___y_2573_, sizeof(void*)*14);
v_cancelTk_x3f_2589_ = lean_ctor_get(v___y_2573_, 12);
v_suppressElabErrors_2590_ = lean_ctor_get_uint8(v___y_2573_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2591_ = lean_ctor_get(v___y_2573_, 13);
v_ref_2592_ = l_Lean_replaceRef(v_ref_2567_, v_ref_2581_);
lean_inc_ref(v_inheritedTraceOptions_2591_);
lean_inc(v_cancelTk_x3f_2589_);
lean_inc(v_currMacroScope_2587_);
lean_inc(v_quotContext_2586_);
lean_inc(v_maxHeartbeats_2585_);
lean_inc(v_initHeartbeats_2584_);
lean_inc(v_openDecls_2583_);
lean_inc(v_currNamespace_2582_);
lean_inc(v_maxRecDepth_2580_);
lean_inc(v_currRecDepth_2579_);
lean_inc_ref(v_options_2578_);
lean_inc_ref(v_fileMap_2577_);
lean_inc_ref(v_fileName_2576_);
v___x_2593_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2593_, 0, v_fileName_2576_);
lean_ctor_set(v___x_2593_, 1, v_fileMap_2577_);
lean_ctor_set(v___x_2593_, 2, v_options_2578_);
lean_ctor_set(v___x_2593_, 3, v_currRecDepth_2579_);
lean_ctor_set(v___x_2593_, 4, v_maxRecDepth_2580_);
lean_ctor_set(v___x_2593_, 5, v_ref_2592_);
lean_ctor_set(v___x_2593_, 6, v_currNamespace_2582_);
lean_ctor_set(v___x_2593_, 7, v_openDecls_2583_);
lean_ctor_set(v___x_2593_, 8, v_initHeartbeats_2584_);
lean_ctor_set(v___x_2593_, 9, v_maxHeartbeats_2585_);
lean_ctor_set(v___x_2593_, 10, v_quotContext_2586_);
lean_ctor_set(v___x_2593_, 11, v_currMacroScope_2587_);
lean_ctor_set(v___x_2593_, 12, v_cancelTk_x3f_2589_);
lean_ctor_set(v___x_2593_, 13, v_inheritedTraceOptions_2591_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*14, v_diag_2588_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*14 + 1, v_suppressElabErrors_2590_);
v___x_2594_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___x_2593_, v___y_2574_);
lean_dec_ref_known(v___x_2593_, 14);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg___boxed(lean_object* v_ref_2595_, lean_object* v_msg_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_ref_2595_, v_msg_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v_ref_2595_);
return v_res_2604_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2605_; double v___x_2606_; 
v___x_2605_ = lean_unsigned_to_nat(0u);
v___x_2606_ = lean_float_of_nat(v___x_2605_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(lean_object* v_cls_2609_, lean_object* v_msg_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v_ref_2616_; lean_object* v___x_2617_; lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2662_; 
v_ref_2616_ = lean_ctor_get(v___y_2613_, 5);
v___x_2617_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msg_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_);
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2620_ = v___x_2617_;
v_isShared_2621_ = v_isSharedCheck_2662_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2617_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2662_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2622_; lean_object* v_traceState_2623_; lean_object* v_env_2624_; lean_object* v_nextMacroScope_2625_; lean_object* v_ngen_2626_; lean_object* v_auxDeclNGen_2627_; lean_object* v_cache_2628_; lean_object* v_messages_2629_; lean_object* v_infoState_2630_; lean_object* v_snapshotTasks_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2661_; 
v___x_2622_ = lean_st_ref_take(v___y_2614_);
v_traceState_2623_ = lean_ctor_get(v___x_2622_, 4);
v_env_2624_ = lean_ctor_get(v___x_2622_, 0);
v_nextMacroScope_2625_ = lean_ctor_get(v___x_2622_, 1);
v_ngen_2626_ = lean_ctor_get(v___x_2622_, 2);
v_auxDeclNGen_2627_ = lean_ctor_get(v___x_2622_, 3);
v_cache_2628_ = lean_ctor_get(v___x_2622_, 5);
v_messages_2629_ = lean_ctor_get(v___x_2622_, 6);
v_infoState_2630_ = lean_ctor_get(v___x_2622_, 7);
v_snapshotTasks_2631_ = lean_ctor_get(v___x_2622_, 8);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2633_ = v___x_2622_;
v_isShared_2634_ = v_isSharedCheck_2661_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_snapshotTasks_2631_);
lean_inc(v_infoState_2630_);
lean_inc(v_messages_2629_);
lean_inc(v_cache_2628_);
lean_inc(v_traceState_2623_);
lean_inc(v_auxDeclNGen_2627_);
lean_inc(v_ngen_2626_);
lean_inc(v_nextMacroScope_2625_);
lean_inc(v_env_2624_);
lean_dec(v___x_2622_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2661_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
uint64_t v_tid_2635_; lean_object* v_traces_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2660_; 
v_tid_2635_ = lean_ctor_get_uint64(v_traceState_2623_, sizeof(void*)*1);
v_traces_2636_ = lean_ctor_get(v_traceState_2623_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v_traceState_2623_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2638_ = v_traceState_2623_;
v_isShared_2639_ = v_isSharedCheck_2660_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_traces_2636_);
lean_dec(v_traceState_2623_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2660_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2640_; double v___x_2641_; uint8_t v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2650_; 
v___x_2640_ = lean_box(0);
v___x_2641_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0);
v___x_2642_ = 0;
v___x_2643_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0));
v___x_2644_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2644_, 0, v_cls_2609_);
lean_ctor_set(v___x_2644_, 1, v___x_2640_);
lean_ctor_set(v___x_2644_, 2, v___x_2643_);
lean_ctor_set_float(v___x_2644_, sizeof(void*)*3, v___x_2641_);
lean_ctor_set_float(v___x_2644_, sizeof(void*)*3 + 8, v___x_2641_);
lean_ctor_set_uint8(v___x_2644_, sizeof(void*)*3 + 16, v___x_2642_);
v___x_2645_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__1));
v___x_2646_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2644_);
lean_ctor_set(v___x_2646_, 1, v_a_2618_);
lean_ctor_set(v___x_2646_, 2, v___x_2645_);
lean_inc(v_ref_2616_);
v___x_2647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2647_, 0, v_ref_2616_);
lean_ctor_set(v___x_2647_, 1, v___x_2646_);
v___x_2648_ = l_Lean_PersistentArray_push___redArg(v_traces_2636_, v___x_2647_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v___x_2648_);
v___x_2650_ = v___x_2638_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2648_);
lean_ctor_set_uint64(v_reuseFailAlloc_2659_, sizeof(void*)*1, v_tid_2635_);
v___x_2650_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2652_; 
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 4, v___x_2650_);
v___x_2652_ = v___x_2633_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_env_2624_);
lean_ctor_set(v_reuseFailAlloc_2658_, 1, v_nextMacroScope_2625_);
lean_ctor_set(v_reuseFailAlloc_2658_, 2, v_ngen_2626_);
lean_ctor_set(v_reuseFailAlloc_2658_, 3, v_auxDeclNGen_2627_);
lean_ctor_set(v_reuseFailAlloc_2658_, 4, v___x_2650_);
lean_ctor_set(v_reuseFailAlloc_2658_, 5, v_cache_2628_);
lean_ctor_set(v_reuseFailAlloc_2658_, 6, v_messages_2629_);
lean_ctor_set(v_reuseFailAlloc_2658_, 7, v_infoState_2630_);
lean_ctor_set(v_reuseFailAlloc_2658_, 8, v_snapshotTasks_2631_);
v___x_2652_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2656_; 
v___x_2653_ = lean_st_ref_put(v___y_2614_, v___x_2652_);
v___x_2654_ = lean_box(0);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v___x_2654_);
v___x_2656_ = v___x_2620_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2654_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___boxed(lean_object* v_cls_2663_, lean_object* v_msg_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_2663_, v_msg_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(lean_object* v_as_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
if (lean_obj_tag(v_as_2674_) == 0)
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2682_ = lean_box(0);
v___x_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
return v___x_2683_;
}
else
{
lean_object* v_options_2684_; uint8_t v_hasTrace_2685_; 
v_options_2684_ = lean_ctor_get(v___y_2679_, 2);
v_hasTrace_2685_ = lean_ctor_get_uint8(v_options_2684_, sizeof(void*)*1);
if (v_hasTrace_2685_ == 0)
{
lean_object* v_tail_2686_; 
v_tail_2686_ = lean_ctor_get(v_as_2674_, 1);
lean_inc(v_tail_2686_);
lean_dec_ref_known(v_as_2674_, 2);
v_as_2674_ = v_tail_2686_;
goto _start;
}
else
{
lean_object* v_head_2688_; lean_object* v_tail_2689_; lean_object* v_fst_2690_; lean_object* v_snd_2691_; lean_object* v_inheritedTraceOptions_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; uint8_t v___x_2695_; 
v_head_2688_ = lean_ctor_get(v_as_2674_, 0);
lean_inc(v_head_2688_);
v_tail_2689_ = lean_ctor_get(v_as_2674_, 1);
lean_inc(v_tail_2689_);
lean_dec_ref_known(v_as_2674_, 2);
v_fst_2690_ = lean_ctor_get(v_head_2688_, 0);
lean_inc_n(v_fst_2690_, 2);
v_snd_2691_ = lean_ctor_get(v_head_2688_, 1);
lean_inc(v_snd_2691_);
lean_dec(v_head_2688_);
v_inheritedTraceOptions_2692_ = lean_ctor_get(v___y_2679_, 13);
v___x_2693_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__1));
v___x_2694_ = l_Lean_Name_append(v___x_2693_, v_fst_2690_);
v___x_2695_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2692_, v_options_2684_, v___x_2694_);
lean_dec(v___x_2694_);
if (v___x_2695_ == 0)
{
lean_dec(v_snd_2691_);
lean_dec(v_fst_2690_);
v_as_2674_ = v_tail_2689_;
goto _start;
}
else
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2697_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2697_, 0, v_snd_2691_);
v___x_2698_ = l_Lean_MessageData_ofFormat(v___x_2697_);
v___x_2699_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_fst_2690_, v___x_2698_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_dec_ref_known(v___x_2699_, 1);
v_as_2674_ = v_tail_2689_;
goto _start;
}
else
{
lean_dec(v_tail_2689_);
return v___x_2699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___boxed(lean_object* v_as_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(v_as_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
return v_res_2709_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(lean_object* v_keys_2710_, lean_object* v_i_2711_, lean_object* v_k_2712_){
_start:
{
lean_object* v___x_2713_; uint8_t v___x_2714_; 
v___x_2713_ = lean_array_get_size(v_keys_2710_);
v___x_2714_ = lean_nat_dec_lt(v_i_2711_, v___x_2713_);
if (v___x_2714_ == 0)
{
lean_dec(v_i_2711_);
return v___x_2714_;
}
else
{
lean_object* v_k_x27_2715_; uint8_t v___x_2716_; 
v_k_x27_2715_ = lean_array_fget_borrowed(v_keys_2710_, v_i_2711_);
v___x_2716_ = l_Lean_instBEqExtraModUse_beq(v_k_2712_, v_k_x27_2715_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = lean_unsigned_to_nat(1u);
v___x_2718_ = lean_nat_add(v_i_2711_, v___x_2717_);
lean_dec(v_i_2711_);
v_i_2711_ = v___x_2718_;
goto _start;
}
else
{
lean_dec(v_i_2711_);
return v___x_2716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg___boxed(lean_object* v_keys_2720_, lean_object* v_i_2721_, lean_object* v_k_2722_){
_start:
{
uint8_t v_res_2723_; lean_object* v_r_2724_; 
v_res_2723_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_keys_2720_, v_i_2721_, v_k_2722_);
lean_dec_ref(v_k_2722_);
lean_dec_ref(v_keys_2720_);
v_r_2724_ = lean_box(v_res_2723_);
return v_r_2724_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(lean_object* v_x_2725_, size_t v_x_2726_, lean_object* v_x_2727_){
_start:
{
if (lean_obj_tag(v_x_2725_) == 0)
{
lean_object* v_es_2728_; lean_object* v___x_2729_; size_t v___x_2730_; size_t v___x_2731_; lean_object* v_j_2732_; lean_object* v___x_2733_; 
v_es_2728_ = lean_ctor_get(v_x_2725_, 0);
v___x_2729_ = lean_box(2);
v___x_2730_ = ((size_t)31ULL);
v___x_2731_ = lean_usize_land(v_x_2726_, v___x_2730_);
v_j_2732_ = lean_usize_to_nat(v___x_2731_);
v___x_2733_ = lean_array_get_borrowed(v___x_2729_, v_es_2728_, v_j_2732_);
lean_dec(v_j_2732_);
switch(lean_obj_tag(v___x_2733_))
{
case 0:
{
lean_object* v_key_2734_; uint8_t v___x_2735_; 
v_key_2734_ = lean_ctor_get(v___x_2733_, 0);
v___x_2735_ = l_Lean_instBEqExtraModUse_beq(v_x_2727_, v_key_2734_);
return v___x_2735_;
}
case 1:
{
lean_object* v_node_2736_; size_t v___x_2737_; size_t v___x_2738_; 
v_node_2736_ = lean_ctor_get(v___x_2733_, 0);
v___x_2737_ = ((size_t)5ULL);
v___x_2738_ = lean_usize_shift_right(v_x_2726_, v___x_2737_);
v_x_2725_ = v_node_2736_;
v_x_2726_ = v___x_2738_;
goto _start;
}
default: 
{
uint8_t v___x_2740_; 
v___x_2740_ = 0;
return v___x_2740_;
}
}
}
else
{
lean_object* v_ks_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; 
v_ks_2741_ = lean_ctor_get(v_x_2725_, 0);
v___x_2742_ = lean_unsigned_to_nat(0u);
v___x_2743_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_ks_2741_, v___x_2742_, v_x_2727_);
return v___x_2743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_x_2744_, lean_object* v_x_2745_, lean_object* v_x_2746_){
_start:
{
size_t v_x_15017__boxed_2747_; uint8_t v_res_2748_; lean_object* v_r_2749_; 
v_x_15017__boxed_2747_ = lean_unbox_usize(v_x_2745_);
lean_dec(v_x_2745_);
v_res_2748_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_2744_, v_x_15017__boxed_2747_, v_x_2746_);
lean_dec_ref(v_x_2746_);
lean_dec_ref(v_x_2744_);
v_r_2749_ = lean_box(v_res_2748_);
return v_r_2749_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(lean_object* v_x_2750_, lean_object* v_x_2751_){
_start:
{
uint64_t v___x_2752_; size_t v___x_2753_; uint8_t v___x_2754_; 
v___x_2752_ = l_Lean_instHashableExtraModUse_hash(v_x_2751_);
v___x_2753_ = lean_uint64_to_usize(v___x_2752_);
v___x_2754_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_2750_, v___x_2753_, v_x_2751_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_x_2755_, lean_object* v_x_2756_){
_start:
{
uint8_t v_res_2757_; lean_object* v_r_2758_; 
v_res_2757_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v_x_2755_, v_x_2756_);
lean_dec_ref(v_x_2756_);
lean_dec_ref(v_x_2755_);
v_r_2758_ = lean_box(v_res_2757_);
return v_r_2758_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2761_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1));
v___x_2762_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0));
v___x_2763_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2762_, v___x_2761_);
return v___x_2763_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2764_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4(void){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3);
v___x_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
return v___x_2766_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4);
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
return v___x_2768_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6(void){
_start:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2769_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4);
v___x_2770_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
lean_ctor_set(v___x_2770_, 1, v___x_2769_);
lean_ctor_set(v___x_2770_, 2, v___x_2769_);
lean_ctor_set(v___x_2770_, 3, v___x_2769_);
lean_ctor_set(v___x_2770_, 4, v___x_2769_);
lean_ctor_set(v___x_2770_, 5, v___x_2769_);
return v___x_2770_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10(void){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2775_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9));
v___x_2776_ = l_Lean_stringToMessageData(v___x_2775_);
return v___x_2776_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12(void){
_start:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2778_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11));
v___x_2779_ = l_Lean_stringToMessageData(v___x_2778_);
return v___x_2779_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13(void){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0));
v___x_2781_ = l_Lean_stringToMessageData(v___x_2780_);
return v___x_2781_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14(void){
_start:
{
lean_object* v_cls_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v_cls_2782_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__8));
v___x_2783_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__1));
v___x_2784_ = l_Lean_Name_append(v___x_2783_, v_cls_2782_);
return v___x_2784_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16(void){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15));
v___x_2787_ = l_Lean_stringToMessageData(v___x_2786_);
return v___x_2787_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18(void){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__17));
v___x_2790_ = l_Lean_stringToMessageData(v___x_2789_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(lean_object* v_mod_2795_, uint8_t v_isMeta_2796_, lean_object* v_hint_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v___x_2805_; lean_object* v_env_2806_; uint8_t v_isExporting_2807_; lean_object* v___x_2808_; lean_object* v_env_2809_; lean_object* v___x_2810_; lean_object* v_entry_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___x_2857_; uint8_t v___x_2858_; 
v___x_2805_ = lean_st_ref_get(v___y_2803_);
v_env_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc_ref(v_env_2806_);
lean_dec(v___x_2805_);
v_isExporting_2807_ = lean_ctor_get_uint8(v_env_2806_, sizeof(void*)*8);
lean_dec_ref(v_env_2806_);
v___x_2808_ = lean_st_ref_get(v___y_2803_);
v_env_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc_ref(v_env_2809_);
lean_dec(v___x_2808_);
v___x_2810_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2);
lean_inc(v_mod_2795_);
v_entry_2811_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2811_, 0, v_mod_2795_);
lean_ctor_set_uint8(v_entry_2811_, sizeof(void*)*1, v_isExporting_2807_);
lean_ctor_set_uint8(v_entry_2811_, sizeof(void*)*1 + 1, v_isMeta_2796_);
v___x_2812_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2813_ = lean_box(1);
v___x_2814_ = lean_box(0);
v___x_2857_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2810_, v___x_2812_, v_env_2809_, v___x_2813_, v___x_2814_);
v___x_2858_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v___x_2857_, v_entry_2811_);
lean_dec(v___x_2857_);
if (v___x_2858_ == 0)
{
lean_object* v_options_2859_; uint8_t v_hasTrace_2860_; 
v_options_2859_ = lean_ctor_get(v___y_2802_, 2);
v_hasTrace_2860_ = lean_ctor_get_uint8(v_options_2859_, sizeof(void*)*1);
if (v_hasTrace_2860_ == 0)
{
lean_dec(v_hint_2797_);
lean_dec(v_mod_2795_);
v___y_2816_ = v___y_2801_;
v___y_2817_ = v___y_2803_;
goto v___jp_2815_;
}
else
{
lean_object* v_inheritedTraceOptions_2861_; lean_object* v_cls_2862_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___x_2882_; uint8_t v___x_2883_; 
v_inheritedTraceOptions_2861_ = lean_ctor_get(v___y_2802_, 13);
v_cls_2862_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__8));
v___x_2882_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14);
v___x_2883_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2861_, v_options_2859_, v___x_2882_);
if (v___x_2883_ == 0)
{
lean_dec(v_hint_2797_);
lean_dec(v_mod_2795_);
v___y_2816_ = v___y_2801_;
v___y_2817_ = v___y_2803_;
goto v___jp_2815_;
}
else
{
lean_object* v___x_2884_; lean_object* v___y_2886_; 
v___x_2884_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16);
if (v_isExporting_2807_ == 0)
{
lean_object* v___x_2893_; 
v___x_2893_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__21));
v___y_2886_ = v___x_2893_;
goto v___jp_2885_;
}
else
{
lean_object* v___x_2894_; 
v___x_2894_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__22));
v___y_2886_ = v___x_2894_;
goto v___jp_2885_;
}
v___jp_2885_:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
lean_inc_ref(v___y_2886_);
v___x_2887_ = l_Lean_stringToMessageData(v___y_2886_);
v___x_2888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2884_);
lean_ctor_set(v___x_2888_, 1, v___x_2887_);
v___x_2889_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18);
v___x_2890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2888_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
if (v_isMeta_2796_ == 0)
{
lean_object* v___x_2891_; 
v___x_2891_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__19));
v___y_2869_ = v___x_2890_;
v___y_2870_ = v___x_2891_;
goto v___jp_2868_;
}
else
{
lean_object* v___x_2892_; 
v___x_2892_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__20));
v___y_2869_ = v___x_2890_;
v___y_2870_ = v___x_2892_;
goto v___jp_2868_;
}
}
}
v___jp_2863_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___y_2864_);
lean_ctor_set(v___x_2866_, 1, v___y_2865_);
v___x_2867_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_2862_, v___x_2866_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_dec_ref_known(v___x_2867_, 1);
v___y_2816_ = v___y_2801_;
v___y_2817_ = v___y_2803_;
goto v___jp_2815_;
}
else
{
lean_dec_ref_known(v_entry_2811_, 1);
return v___x_2867_;
}
}
v___jp_2868_:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
lean_inc_ref(v___y_2870_);
v___x_2871_ = l_Lean_stringToMessageData(v___y_2870_);
v___x_2872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___y_2869_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10);
v___x_2874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2872_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
v___x_2875_ = l_Lean_MessageData_ofName(v_mod_2795_);
v___x_2876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2874_);
lean_ctor_set(v___x_2876_, 1, v___x_2875_);
v___x_2877_ = l_Lean_Name_isAnonymous(v_hint_2797_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2878_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12);
v___x_2879_ = l_Lean_MessageData_ofName(v_hint_2797_);
v___x_2880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2878_);
lean_ctor_set(v___x_2880_, 1, v___x_2879_);
v___y_2864_ = v___x_2876_;
v___y_2865_ = v___x_2880_;
goto v___jp_2863_;
}
else
{
lean_object* v___x_2881_; 
lean_dec(v_hint_2797_);
v___x_2881_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13);
v___y_2864_ = v___x_2876_;
v___y_2865_ = v___x_2881_;
goto v___jp_2863_;
}
}
}
}
else
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
lean_dec_ref_known(v_entry_2811_, 1);
lean_dec(v_hint_2797_);
lean_dec(v_mod_2795_);
v___x_2895_ = lean_box(0);
v___x_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
return v___x_2896_;
}
v___jp_2815_:
{
lean_object* v___x_2818_; lean_object* v_toEnvExtension_2819_; lean_object* v_env_2820_; lean_object* v_nextMacroScope_2821_; lean_object* v_ngen_2822_; lean_object* v_auxDeclNGen_2823_; lean_object* v_traceState_2824_; lean_object* v_messages_2825_; lean_object* v_infoState_2826_; lean_object* v_snapshotTasks_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2855_; 
v___x_2818_ = lean_st_ref_take(v___y_2817_);
v_toEnvExtension_2819_ = lean_ctor_get(v___x_2812_, 0);
v_env_2820_ = lean_ctor_get(v___x_2818_, 0);
v_nextMacroScope_2821_ = lean_ctor_get(v___x_2818_, 1);
v_ngen_2822_ = lean_ctor_get(v___x_2818_, 2);
v_auxDeclNGen_2823_ = lean_ctor_get(v___x_2818_, 3);
v_traceState_2824_ = lean_ctor_get(v___x_2818_, 4);
v_messages_2825_ = lean_ctor_get(v___x_2818_, 6);
v_infoState_2826_ = lean_ctor_get(v___x_2818_, 7);
v_snapshotTasks_2827_ = lean_ctor_get(v___x_2818_, 8);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; 
v_unused_2856_ = lean_ctor_get(v___x_2818_, 5);
lean_dec(v_unused_2856_);
v___x_2829_ = v___x_2818_;
v_isShared_2830_ = v_isSharedCheck_2855_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_snapshotTasks_2827_);
lean_inc(v_infoState_2826_);
lean_inc(v_messages_2825_);
lean_inc(v_traceState_2824_);
lean_inc(v_auxDeclNGen_2823_);
lean_inc(v_ngen_2822_);
lean_inc(v_nextMacroScope_2821_);
lean_inc(v_env_2820_);
lean_dec(v___x_2818_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2855_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v_asyncMode_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2835_; 
v_asyncMode_2831_ = lean_ctor_get(v_toEnvExtension_2819_, 2);
v___x_2832_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2812_, v_env_2820_, v_entry_2811_, v_asyncMode_2831_, v___x_2814_);
v___x_2833_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 5, v___x_2833_);
lean_ctor_set(v___x_2829_, 0, v___x_2832_);
v___x_2835_ = v___x_2829_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2832_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_nextMacroScope_2821_);
lean_ctor_set(v_reuseFailAlloc_2854_, 2, v_ngen_2822_);
lean_ctor_set(v_reuseFailAlloc_2854_, 3, v_auxDeclNGen_2823_);
lean_ctor_set(v_reuseFailAlloc_2854_, 4, v_traceState_2824_);
lean_ctor_set(v_reuseFailAlloc_2854_, 5, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2854_, 6, v_messages_2825_);
lean_ctor_set(v_reuseFailAlloc_2854_, 7, v_infoState_2826_);
lean_ctor_set(v_reuseFailAlloc_2854_, 8, v_snapshotTasks_2827_);
v___x_2835_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v_mctx_2838_; lean_object* v_zetaDeltaFVarIds_2839_; lean_object* v_postponed_2840_; lean_object* v_diag_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2852_; 
v___x_2836_ = lean_st_ref_put(v___y_2817_, v___x_2835_);
v___x_2837_ = lean_st_ref_take(v___y_2816_);
v_mctx_2838_ = lean_ctor_get(v___x_2837_, 0);
v_zetaDeltaFVarIds_2839_ = lean_ctor_get(v___x_2837_, 2);
v_postponed_2840_ = lean_ctor_get(v___x_2837_, 3);
v_diag_2841_ = lean_ctor_get(v___x_2837_, 4);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2852_ == 0)
{
lean_object* v_unused_2853_; 
v_unused_2853_ = lean_ctor_get(v___x_2837_, 1);
lean_dec(v_unused_2853_);
v___x_2843_ = v___x_2837_;
v_isShared_2844_ = v_isSharedCheck_2852_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_diag_2841_);
lean_inc(v_postponed_2840_);
lean_inc(v_zetaDeltaFVarIds_2839_);
lean_inc(v_mctx_2838_);
lean_dec(v___x_2837_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2852_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2845_; lean_object* v___x_2847_; 
v___x_2845_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 1, v___x_2845_);
v___x_2847_ = v___x_2843_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_mctx_2838_);
lean_ctor_set(v_reuseFailAlloc_2851_, 1, v___x_2845_);
lean_ctor_set(v_reuseFailAlloc_2851_, 2, v_zetaDeltaFVarIds_2839_);
lean_ctor_set(v_reuseFailAlloc_2851_, 3, v_postponed_2840_);
lean_ctor_set(v_reuseFailAlloc_2851_, 4, v_diag_2841_);
v___x_2847_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2848_ = lean_st_ref_put(v___y_2816_, v___x_2847_);
v___x_2849_ = lean_box(0);
v___x_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
return v___x_2850_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___boxed(lean_object* v_mod_2897_, lean_object* v_isMeta_2898_, lean_object* v_hint_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
uint8_t v_isMeta_boxed_2907_; lean_object* v_res_2908_; 
v_isMeta_boxed_2907_ = lean_unbox(v_isMeta_2898_);
v_res_2908_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_mod_2897_, v_isMeta_boxed_2907_, v_hint_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(lean_object* v___x_2909_, lean_object* v_declName_2910_, lean_object* v_as_2911_, size_t v_sz_2912_, size_t v_i_2913_, lean_object* v_b_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
uint8_t v___x_2922_; 
v___x_2922_ = lean_usize_dec_lt(v_i_2913_, v_sz_2912_);
if (v___x_2922_ == 0)
{
lean_object* v___x_2923_; 
lean_dec(v_declName_2910_);
v___x_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2923_, 0, v_b_2914_);
return v___x_2923_;
}
else
{
lean_object* v___x_2924_; lean_object* v_modules_2925_; lean_object* v___x_2926_; lean_object* v_a_2927_; lean_object* v___x_2928_; lean_object* v_toImport_2929_; lean_object* v_module_2930_; uint8_t v___x_2931_; lean_object* v___x_2932_; 
v___x_2924_ = l_Lean_Environment_header(v___x_2909_);
v_modules_2925_ = lean_ctor_get(v___x_2924_, 3);
lean_inc_ref(v_modules_2925_);
lean_dec_ref(v___x_2924_);
v___x_2926_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2927_ = lean_array_uget_borrowed(v_as_2911_, v_i_2913_);
v___x_2928_ = lean_array_get(v___x_2926_, v_modules_2925_, v_a_2927_);
lean_dec_ref(v_modules_2925_);
v_toImport_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc_ref(v_toImport_2929_);
lean_dec(v___x_2928_);
v_module_2930_ = lean_ctor_get(v_toImport_2929_, 0);
lean_inc(v_module_2930_);
lean_dec_ref(v_toImport_2929_);
v___x_2931_ = 0;
lean_inc(v_declName_2910_);
v___x_2932_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_module_2930_, v___x_2931_, v_declName_2910_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v___x_2933_; size_t v___x_2934_; size_t v___x_2935_; 
lean_dec_ref_known(v___x_2932_, 1);
v___x_2933_ = lean_box(0);
v___x_2934_ = ((size_t)1ULL);
v___x_2935_ = lean_usize_add(v_i_2913_, v___x_2934_);
v_i_2913_ = v___x_2935_;
v_b_2914_ = v___x_2933_;
goto _start;
}
else
{
lean_dec(v_declName_2910_);
return v___x_2932_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5___boxed(lean_object* v___x_2937_, lean_object* v_declName_2938_, lean_object* v_as_2939_, lean_object* v_sz_2940_, lean_object* v_i_2941_, lean_object* v_b_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
size_t v_sz_boxed_2950_; size_t v_i_boxed_2951_; lean_object* v_res_2952_; 
v_sz_boxed_2950_ = lean_unbox_usize(v_sz_2940_);
lean_dec(v_sz_2940_);
v_i_boxed_2951_ = lean_unbox_usize(v_i_2941_);
lean_dec(v_i_2941_);
v_res_2952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(v___x_2937_, v_declName_2938_, v_as_2939_, v_sz_boxed_2950_, v_i_boxed_2951_, v_b_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec_ref(v_as_2939_);
lean_dec_ref(v___x_2937_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15_spec__18___redArg(lean_object* v_m_2953_, lean_object* v_query_2954_, lean_object* v_x_2955_, lean_object* v_x_2956_, lean_object* v_x_2957_){
_start:
{
lean_object* v_zero_2958_; uint8_t v_isZero_2959_; 
v_zero_2958_ = lean_unsigned_to_nat(0u);
v_isZero_2959_ = lean_nat_dec_eq(v_x_2956_, v_zero_2958_);
if (v_isZero_2959_ == 1)
{
lean_dec(v_x_2957_);
lean_dec(v_x_2956_);
if (lean_obj_tag(v_x_2955_) == 0)
{
lean_object* v___x_2960_; 
v___x_2960_ = lean_box(2);
return v___x_2960_;
}
else
{
lean_object* v_val_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
v_val_2961_ = lean_ctor_get(v_x_2955_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v_x_2955_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v_x_2955_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_val_2961_);
lean_dec(v_x_2955_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_val_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
else
{
lean_object* v_keyArray_2969_; lean_object* v_valueArray_2970_; lean_object* v___x_2971_; uint8_t v_isSome_2972_; 
v_keyArray_2969_ = lean_ctor_get(v_m_2953_, 1);
v_valueArray_2970_ = lean_ctor_get(v_m_2953_, 2);
v___x_2971_ = lean_array_fget_borrowed(v_keyArray_2969_, v_x_2957_);
v_isSome_2972_ = lean_noption_is_some(v___x_2971_);
if (v_isSome_2972_ == 0)
{
lean_dec(v_x_2956_);
if (lean_obj_tag(v_x_2955_) == 0)
{
lean_object* v___x_2973_; 
v___x_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2973_, 0, v_x_2957_);
return v___x_2973_;
}
else
{
lean_object* v_val_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_dec(v_x_2957_);
v_val_2974_ = lean_ctor_get(v_x_2955_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_x_2955_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v_x_2955_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_val_2974_);
lean_dec(v_x_2955_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_val_2974_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
else
{
lean_object* v_one_2982_; lean_object* v_n_2983_; lean_object* v___y_2985_; 
v_one_2982_ = lean_unsigned_to_nat(1u);
v_n_2983_ = lean_nat_sub(v_x_2956_, v_one_2982_);
lean_dec(v_x_2956_);
if (v_isSome_2972_ == 0)
{
goto v___jp_2991_;
}
else
{
lean_object* v___x_2993_; uint8_t v_isSome_2994_; 
v___x_2993_ = lean_array_fget_borrowed(v_valueArray_2970_, v_x_2957_);
v_isSome_2994_ = lean_noption_is_some(v___x_2993_);
if (v_isSome_2994_ == 0)
{
goto v___jp_2991_;
}
else
{
lean_object* v_val_2995_; uint8_t v___x_2996_; 
lean_inc(v___x_2971_);
v_val_2995_ = lean_noption_get(v___x_2971_);
v___x_2996_ = lean_name_eq(v_val_2995_, v_query_2954_);
if (v___x_2996_ == 0)
{
lean_object* v___x_2997_; lean_object* v___x_2998_; uint8_t v___x_2999_; 
lean_dec(v_val_2995_);
v___x_2997_ = lean_array_get_size(v_keyArray_2969_);
v___x_2998_ = lean_nat_add(v_x_2957_, v_one_2982_);
lean_dec(v_x_2957_);
v___x_2999_ = lean_nat_dec_lt(v___x_2998_, v___x_2997_);
if (v___x_2999_ == 0)
{
lean_dec(v___x_2998_);
v_x_2956_ = v_n_2983_;
v_x_2957_ = v_zero_2958_;
goto _start;
}
else
{
v_x_2956_ = v_n_2983_;
v_x_2957_ = v___x_2998_;
goto _start;
}
}
else
{
lean_object* v_val_3002_; lean_object* v___x_3003_; 
lean_dec(v_n_2983_);
lean_dec(v_x_2955_);
lean_inc(v___x_2993_);
v_val_3002_ = lean_noption_get(v___x_2993_);
v___x_3003_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3003_, 0, v_x_2957_);
lean_ctor_set(v___x_3003_, 1, v_val_2995_);
lean_ctor_set(v___x_3003_, 2, v_val_3002_);
return v___x_3003_;
}
}
}
v___jp_2984_:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; uint8_t v___x_2988_; 
v___x_2986_ = lean_array_get_size(v_keyArray_2969_);
v___x_2987_ = lean_nat_add(v_x_2957_, v_one_2982_);
lean_dec(v_x_2957_);
v___x_2988_ = lean_nat_dec_lt(v___x_2987_, v___x_2986_);
if (v___x_2988_ == 0)
{
lean_dec(v___x_2987_);
v_x_2955_ = v___y_2985_;
v_x_2956_ = v_n_2983_;
v_x_2957_ = v_zero_2958_;
goto _start;
}
else
{
v_x_2955_ = v___y_2985_;
v_x_2956_ = v_n_2983_;
v_x_2957_ = v___x_2987_;
goto _start;
}
}
v___jp_2991_:
{
if (lean_obj_tag(v_x_2955_) == 0)
{
lean_object* v___x_2992_; 
lean_inc(v_x_2957_);
v___x_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2992_, 0, v_x_2957_);
v___y_2985_ = v___x_2992_;
goto v___jp_2984_;
}
else
{
v___y_2985_ = v_x_2955_;
goto v___jp_2984_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15_spec__18___redArg___boxed(lean_object* v_m_3004_, lean_object* v_query_3005_, lean_object* v_x_3006_, lean_object* v_x_3007_, lean_object* v_x_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15_spec__18___redArg(v_m_3004_, v_query_3005_, v_x_3006_, v_x_3007_, v_x_3008_);
lean_dec(v_query_3005_);
lean_dec_ref(v_m_3004_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15___redArg(lean_object* v_m_3010_, lean_object* v_query_3011_){
_start:
{
lean_object* v_keyArray_3012_; lean_object* v___x_3013_; uint64_t v___y_3015_; 
v_keyArray_3012_ = lean_ctor_get(v_m_3010_, 1);
v___x_3013_ = lean_array_get_size(v_keyArray_3012_);
if (lean_obj_tag(v_query_3011_) == 0)
{
uint64_t v___x_3030_; 
v___x_3030_ = 1723ULL;
v___y_3015_ = v___x_3030_;
goto v___jp_3014_;
}
else
{
uint64_t v_hash_3031_; 
v_hash_3031_ = lean_ctor_get_uint64(v_query_3011_, sizeof(void*)*2);
v___y_3015_ = v_hash_3031_;
goto v___jp_3014_;
}
v___jp_3014_:
{
uint64_t v___x_3016_; uint64_t v___x_3017_; uint64_t v_fold_3018_; uint64_t v___x_3019_; uint64_t v___x_3020_; uint64_t v___x_3021_; size_t v___x_3022_; size_t v___x_3023_; size_t v___x_3024_; size_t v___x_3025_; size_t v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3016_ = 32ULL;
v___x_3017_ = lean_uint64_shift_right(v___y_3015_, v___x_3016_);
v_fold_3018_ = lean_uint64_xor(v___y_3015_, v___x_3017_);
v___x_3019_ = 16ULL;
v___x_3020_ = lean_uint64_shift_right(v_fold_3018_, v___x_3019_);
v___x_3021_ = lean_uint64_xor(v_fold_3018_, v___x_3020_);
v___x_3022_ = lean_uint64_to_usize(v___x_3021_);
v___x_3023_ = lean_usize_of_nat(v___x_3013_);
v___x_3024_ = ((size_t)1ULL);
v___x_3025_ = lean_usize_sub(v___x_3023_, v___x_3024_);
v___x_3026_ = lean_usize_land(v___x_3022_, v___x_3025_);
v___x_3027_ = lean_usize_to_nat(v___x_3026_);
v___x_3028_ = lean_box(0);
v___x_3029_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15_spec__18___redArg(v_m_3010_, v_query_3011_, v___x_3028_, v___x_3013_, v___x_3027_);
return v___x_3029_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15___redArg___boxed(lean_object* v_m_3032_, lean_object* v_query_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15___redArg(v_m_3032_, v_query_3033_);
lean_dec(v_query_3033_);
lean_dec_ref(v_m_3032_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(lean_object* v_m_3035_, lean_object* v_query_3036_){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15___redArg(v_m_3035_, v_query_3036_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_index_3038_; lean_object* v_key_3039_; lean_object* v_value_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
v_index_3038_ = lean_ctor_get(v___x_3037_, 0);
v_key_3039_ = lean_ctor_get(v___x_3037_, 1);
v_value_3040_ = lean_ctor_get(v___x_3037_, 2);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_3037_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_value_3040_);
lean_inc(v_key_3039_);
lean_inc(v_index_3038_);
lean_dec(v___x_3037_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
if (v_isShared_3043_ == 0)
{
v___x_3045_ = v___x_3042_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_index_3038_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v_key_3039_);
lean_ctor_set(v_reuseFailAlloc_3046_, 2, v_value_3040_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
else
{
lean_object* v___x_3048_; 
lean_dec(v___x_3037_);
v___x_3048_ = lean_box(1);
return v___x_3048_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_m_3049_, lean_object* v_query_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(v_m_3049_, v_query_3050_);
lean_dec(v_query_3050_);
lean_dec_ref(v_m_3049_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(lean_object* v_m_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v___x_3054_; 
v___x_3054_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(v_m_3052_, v_a_3053_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v_value_3055_; lean_object* v___x_3056_; 
v_value_3055_ = lean_ctor_get(v___x_3054_, 2);
lean_inc(v_value_3055_);
lean_dec_ref_known(v___x_3054_, 3);
v___x_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3056_, 0, v_value_3055_);
return v___x_3056_;
}
else
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_box(0);
return v___x_3057_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_m_3058_, lean_object* v_a_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(v_m_3058_, v_a_3059_);
lean_dec(v_a_3059_);
lean_dec_ref(v_m_3058_);
return v_res_3060_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3063_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__1));
v___x_3064_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0));
v___x_3065_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_3064_, v___x_3063_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(lean_object* v_declName_3068_, uint8_t v_isMeta_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v___x_3077_; lean_object* v_env_3081_; lean_object* v___y_3083_; lean_object* v___x_3096_; 
v___x_3077_ = lean_st_ref_get(v___y_3075_);
v_env_3081_ = lean_ctor_get(v___x_3077_, 0);
lean_inc_ref(v_env_3081_);
lean_dec(v___x_3077_);
v___x_3096_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3081_, v_declName_3068_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_dec_ref(v_env_3081_);
lean_dec(v_declName_3068_);
goto v___jp_3078_;
}
else
{
lean_object* v_val_3097_; lean_object* v___x_3098_; lean_object* v_modules_3099_; lean_object* v___x_3100_; uint8_t v___x_3101_; 
v_val_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_val_3097_);
lean_dec_ref_known(v___x_3096_, 1);
v___x_3098_ = l_Lean_Environment_header(v_env_3081_);
v_modules_3099_ = lean_ctor_get(v___x_3098_, 3);
lean_inc_ref(v_modules_3099_);
lean_dec_ref(v___x_3098_);
v___x_3100_ = lean_array_get_size(v_modules_3099_);
v___x_3101_ = lean_nat_dec_lt(v_val_3097_, v___x_3100_);
if (v___x_3101_ == 0)
{
lean_dec_ref(v_modules_3099_);
lean_dec(v_val_3097_);
lean_dec_ref(v_env_3081_);
lean_dec(v_declName_3068_);
goto v___jp_3078_;
}
else
{
lean_object* v___x_3102_; lean_object* v_env_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; uint8_t v___y_3107_; 
v___x_3102_ = lean_st_ref_get(v___y_3075_);
v_env_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc_ref(v_env_3103_);
lean_dec(v___x_3102_);
v___x_3104_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__2);
v___x_3105_ = lean_array_fget(v_modules_3099_, v_val_3097_);
lean_dec(v_val_3097_);
lean_dec_ref(v_modules_3099_);
if (v_isMeta_3069_ == 0)
{
lean_dec_ref(v_env_3103_);
v___y_3107_ = v_isMeta_3069_;
goto v___jp_3106_;
}
else
{
uint8_t v___x_3118_; 
lean_inc(v_declName_3068_);
v___x_3118_ = l_Lean_isMarkedMeta(v_env_3103_, v_declName_3068_);
if (v___x_3118_ == 0)
{
v___y_3107_ = v_isMeta_3069_;
goto v___jp_3106_;
}
else
{
uint8_t v___x_3119_; 
v___x_3119_ = 0;
v___y_3107_ = v___x_3119_;
goto v___jp_3106_;
}
}
v___jp_3106_:
{
lean_object* v_toImport_3108_; lean_object* v_module_3109_; lean_object* v___x_3110_; 
v_toImport_3108_ = lean_ctor_get(v___x_3105_, 0);
lean_inc_ref(v_toImport_3108_);
lean_dec(v___x_3105_);
v_module_3109_ = lean_ctor_get(v_toImport_3108_, 0);
lean_inc(v_module_3109_);
lean_dec_ref(v_toImport_3108_);
lean_inc(v_declName_3068_);
v___x_3110_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_module_3109_, v___y_3107_, v_declName_3068_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
lean_dec_ref_known(v___x_3110_, 1);
v___x_3111_ = l_Lean_indirectModUseExt;
v___x_3112_ = lean_box(1);
v___x_3113_ = lean_box(0);
lean_inc_ref(v_env_3081_);
v___x_3114_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3104_, v___x_3111_, v_env_3081_, v___x_3112_, v___x_3113_);
v___x_3115_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(v___x_3114_, v_declName_3068_);
lean_dec(v___x_3114_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v___x_3116_; 
v___x_3116_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__3));
v___y_3083_ = v___x_3116_;
goto v___jp_3082_;
}
else
{
lean_object* v_val_3117_; 
v_val_3117_ = lean_ctor_get(v___x_3115_, 0);
lean_inc(v_val_3117_);
lean_dec_ref_known(v___x_3115_, 1);
v___y_3083_ = v_val_3117_;
goto v___jp_3082_;
}
}
else
{
lean_dec_ref(v_env_3081_);
lean_dec(v_declName_3068_);
return v___x_3110_;
}
}
}
}
v___jp_3078_:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = lean_box(0);
v___x_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3079_);
return v___x_3080_;
}
v___jp_3082_:
{
lean_object* v___x_3084_; size_t v_sz_3085_; size_t v___x_3086_; lean_object* v___x_3087_; 
v___x_3084_ = lean_box(0);
v_sz_3085_ = lean_array_size(v___y_3083_);
v___x_3086_ = ((size_t)0ULL);
v___x_3087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(v_env_3081_, v_declName_3068_, v___y_3083_, v_sz_3085_, v___x_3086_, v___x_3084_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
lean_dec_ref(v___y_3083_);
lean_dec_ref(v_env_3081_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3094_ == 0)
{
lean_object* v_unused_3095_; 
v_unused_3095_ = lean_ctor_get(v___x_3087_, 0);
lean_dec(v_unused_3095_);
v___x_3089_ = v___x_3087_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_dec(v___x_3087_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v___x_3084_);
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3084_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
else
{
return v___x_3087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___boxed(lean_object* v_declName_3120_, lean_object* v_isMeta_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
uint8_t v_isMeta_boxed_3129_; lean_object* v_res_3130_; 
v_isMeta_boxed_3129_ = lean_unbox(v_isMeta_3121_);
v_res_3130_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(v_declName_3120_, v_isMeta_boxed_3129_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(lean_object* v_as_x27_3131_, lean_object* v_b_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
if (lean_obj_tag(v_as_x27_3131_) == 0)
{
lean_object* v___x_3140_; 
v___x_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3140_, 0, v_b_3132_);
return v___x_3140_;
}
else
{
lean_object* v_head_3141_; lean_object* v_tail_3142_; uint8_t v___x_3143_; lean_object* v___x_3144_; 
v_head_3141_ = lean_ctor_get(v_as_x27_3131_, 0);
v_tail_3142_ = lean_ctor_get(v_as_x27_3131_, 1);
v___x_3143_ = 1;
lean_inc(v_head_3141_);
v___x_3144_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(v_head_3141_, v___x_3143_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v___x_3145_; 
lean_dec_ref_known(v___x_3144_, 1);
v___x_3145_ = lean_box(0);
v_as_x27_3131_ = v_tail_3142_;
v_b_3132_ = v___x_3145_;
goto _start;
}
else
{
return v___x_3144_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_3147_, lean_object* v_b_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_as_x27_3147_, v_b_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v_as_x27_3147_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4(lean_object* v_env_3157_, lean_object* v_options_3158_, lean_object* v_currNamespace_3159_, lean_object* v_openDecls_3160_, lean_object* v_n_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3164_ = l_Lean_ResolveName_resolveGlobalName(v_env_3157_, v_options_3158_, v_currNamespace_3159_, v_openDecls_3160_, v_n_3161_);
v___x_3165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
lean_ctor_set(v___x_3165_, 1, v___y_3163_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4___boxed(lean_object* v_env_3166_, lean_object* v_options_3167_, lean_object* v_currNamespace_3168_, lean_object* v_openDecls_3169_, lean_object* v_n_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4(v_env_3166_, v_options_3167_, v_currNamespace_3168_, v_openDecls_3169_, v_n_3170_, v___y_3171_, v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec_ref(v_options_3167_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2(lean_object* v_env_3174_, lean_object* v_currNamespace_3175_, lean_object* v_openDecls_3176_, lean_object* v_n_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3180_ = l_Lean_ResolveName_resolveNamespace(v_env_3174_, v_currNamespace_3175_, v_openDecls_3176_, v_n_3177_);
v___x_3181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
lean_ctor_set(v___x_3181_, 1, v___y_3179_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2___boxed(lean_object* v_env_3182_, lean_object* v_currNamespace_3183_, lean_object* v_openDecls_3184_, lean_object* v_n_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2(v_env_3182_, v_currNamespace_3183_, v_openDecls_3184_, v_n_3185_, v___y_3186_, v___y_3187_);
lean_dec_ref(v___y_3186_);
return v_res_3188_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3189_ = lean_box(0);
v___x_3190_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
lean_ctor_set(v___x_3191_, 1, v___x_3189_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg(){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0);
v___x_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3193_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___boxed(lean_object* v___y_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
return v_res_3196_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = l_Lean_maxRecDepthErrorMessage;
v___x_3203_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
return v___x_3203_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3204_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3);
v___x_3205_ = l_Lean_MessageData_ofFormat(v___x_3204_);
return v___x_3205_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3206_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4);
v___x_3207_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__2));
v___x_3208_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3207_);
lean_ctor_set(v___x_3208_, 1, v___x_3206_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(lean_object* v_ref_3209_){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3211_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5);
v___x_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3212_, 0, v_ref_3209_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
v___x_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___boxed(lean_object* v_ref_3214_, lean_object* v___y_3215_){
_start:
{
lean_object* v_res_3216_; 
v_res_3216_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_ref_3214_);
return v_res_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(lean_object* v_x_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v___x_3226_; lean_object* v_env_3227_; lean_object* v_options_3228_; lean_object* v_currRecDepth_3229_; lean_object* v_maxRecDepth_3230_; lean_object* v_ref_3231_; lean_object* v_currNamespace_3232_; lean_object* v_openDecls_3233_; lean_object* v_quotContext_3234_; lean_object* v_currMacroScope_3235_; lean_object* v___x_3236_; lean_object* v_nextMacroScope_3237_; lean_object* v___f_3238_; lean_object* v___f_3239_; lean_object* v___f_3240_; lean_object* v___f_3241_; lean_object* v___f_3242_; lean_object* v_methods_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3226_ = lean_st_ref_get(v___y_3224_);
v_env_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc_ref_n(v_env_3227_, 4);
lean_dec(v___x_3226_);
v_options_3228_ = lean_ctor_get(v___y_3223_, 2);
v_currRecDepth_3229_ = lean_ctor_get(v___y_3223_, 3);
v_maxRecDepth_3230_ = lean_ctor_get(v___y_3223_, 4);
v_ref_3231_ = lean_ctor_get(v___y_3223_, 5);
v_currNamespace_3232_ = lean_ctor_get(v___y_3223_, 6);
v_openDecls_3233_ = lean_ctor_get(v___y_3223_, 7);
v_quotContext_3234_ = lean_ctor_get(v___y_3223_, 10);
v_currMacroScope_3235_ = lean_ctor_get(v___y_3223_, 11);
v___x_3236_ = lean_st_ref_get(v___y_3224_);
v_nextMacroScope_3237_ = lean_ctor_get(v___x_3236_, 1);
lean_inc(v_nextMacroScope_3237_);
lean_dec(v___x_3236_);
v___f_3238_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3238_, 0, v_env_3227_);
v___f_3239_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_3239_, 0, v_env_3227_);
lean_inc_n(v_openDecls_3233_, 2);
lean_inc_n(v_currNamespace_3232_, 3);
v___f_3240_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3240_, 0, v_env_3227_);
lean_closure_set(v___f_3240_, 1, v_currNamespace_3232_);
lean_closure_set(v___f_3240_, 2, v_openDecls_3233_);
v___f_3241_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3241_, 0, v_currNamespace_3232_);
lean_inc_ref(v_options_3228_);
v___f_3242_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_3242_, 0, v_env_3227_);
lean_closure_set(v___f_3242_, 1, v_options_3228_);
lean_closure_set(v___f_3242_, 2, v_currNamespace_3232_);
lean_closure_set(v___f_3242_, 3, v_openDecls_3233_);
v_methods_3243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_3243_, 0, v___f_3238_);
lean_ctor_set(v_methods_3243_, 1, v___f_3241_);
lean_ctor_set(v_methods_3243_, 2, v___f_3239_);
lean_ctor_set(v_methods_3243_, 3, v___f_3240_);
lean_ctor_set(v_methods_3243_, 4, v___f_3242_);
lean_inc(v_ref_3231_);
lean_inc(v_maxRecDepth_3230_);
lean_inc(v_currRecDepth_3229_);
lean_inc(v_currMacroScope_3235_);
lean_inc(v_quotContext_3234_);
v___x_3244_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3244_, 0, v_methods_3243_);
lean_ctor_set(v___x_3244_, 1, v_quotContext_3234_);
lean_ctor_set(v___x_3244_, 2, v_currMacroScope_3235_);
lean_ctor_set(v___x_3244_, 3, v_currRecDepth_3229_);
lean_ctor_set(v___x_3244_, 4, v_maxRecDepth_3230_);
lean_ctor_set(v___x_3244_, 5, v_ref_3231_);
v___x_3245_ = lean_box(0);
v___x_3246_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3246_, 0, v_nextMacroScope_3237_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
lean_ctor_set(v___x_3246_, 2, v___x_3245_);
v___x_3247_ = lean_apply_2(v_x_3218_, v___x_3244_, v___x_3246_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; lean_object* v_a_3249_; lean_object* v_macroScope_3250_; lean_object* v_traceMsgs_3251_; lean_object* v_expandedMacroDecls_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 1);
lean_inc(v_a_3248_);
v_a_3249_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_a_3249_);
lean_dec_ref_known(v___x_3247_, 2);
v_macroScope_3250_ = lean_ctor_get(v_a_3248_, 0);
lean_inc(v_macroScope_3250_);
v_traceMsgs_3251_ = lean_ctor_get(v_a_3248_, 1);
lean_inc(v_traceMsgs_3251_);
v_expandedMacroDecls_3252_ = lean_ctor_get(v_a_3248_, 2);
lean_inc(v_expandedMacroDecls_3252_);
lean_dec(v_a_3248_);
v___x_3253_ = lean_box(0);
v___x_3254_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_expandedMacroDecls_3252_, v___x_3253_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
lean_dec(v_expandedMacroDecls_3252_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v___x_3255_; lean_object* v_env_3256_; lean_object* v_ngen_3257_; lean_object* v_auxDeclNGen_3258_; lean_object* v_traceState_3259_; lean_object* v_cache_3260_; lean_object* v_messages_3261_; lean_object* v_infoState_3262_; lean_object* v_snapshotTasks_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3289_; 
lean_dec_ref_known(v___x_3254_, 1);
v___x_3255_ = lean_st_ref_take(v___y_3224_);
v_env_3256_ = lean_ctor_get(v___x_3255_, 0);
v_ngen_3257_ = lean_ctor_get(v___x_3255_, 2);
v_auxDeclNGen_3258_ = lean_ctor_get(v___x_3255_, 3);
v_traceState_3259_ = lean_ctor_get(v___x_3255_, 4);
v_cache_3260_ = lean_ctor_get(v___x_3255_, 5);
v_messages_3261_ = lean_ctor_get(v___x_3255_, 6);
v_infoState_3262_ = lean_ctor_get(v___x_3255_, 7);
v_snapshotTasks_3263_ = lean_ctor_get(v___x_3255_, 8);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3289_ == 0)
{
lean_object* v_unused_3290_; 
v_unused_3290_ = lean_ctor_get(v___x_3255_, 1);
lean_dec(v_unused_3290_);
v___x_3265_ = v___x_3255_;
v_isShared_3266_ = v_isSharedCheck_3289_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_snapshotTasks_3263_);
lean_inc(v_infoState_3262_);
lean_inc(v_messages_3261_);
lean_inc(v_cache_3260_);
lean_inc(v_traceState_3259_);
lean_inc(v_auxDeclNGen_3258_);
lean_inc(v_ngen_3257_);
lean_inc(v_env_3256_);
lean_dec(v___x_3255_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3289_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3268_; 
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 1, v_macroScope_3250_);
v___x_3268_ = v___x_3265_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_env_3256_);
lean_ctor_set(v_reuseFailAlloc_3288_, 1, v_macroScope_3250_);
lean_ctor_set(v_reuseFailAlloc_3288_, 2, v_ngen_3257_);
lean_ctor_set(v_reuseFailAlloc_3288_, 3, v_auxDeclNGen_3258_);
lean_ctor_set(v_reuseFailAlloc_3288_, 4, v_traceState_3259_);
lean_ctor_set(v_reuseFailAlloc_3288_, 5, v_cache_3260_);
lean_ctor_set(v_reuseFailAlloc_3288_, 6, v_messages_3261_);
lean_ctor_set(v_reuseFailAlloc_3288_, 7, v_infoState_3262_);
lean_ctor_set(v_reuseFailAlloc_3288_, 8, v_snapshotTasks_3263_);
v___x_3268_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3269_ = lean_st_ref_put(v___y_3224_, v___x_3268_);
v___x_3270_ = l_List_reverse___redArg(v_traceMsgs_3251_);
v___x_3271_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(v___x_3270_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3278_ == 0)
{
lean_object* v_unused_3279_; 
v_unused_3279_ = lean_ctor_get(v___x_3271_, 0);
lean_dec(v_unused_3279_);
v___x_3273_ = v___x_3271_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_dec(v___x_3271_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 0, v_a_3249_);
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3249_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
else
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
lean_dec(v_a_3249_);
v_a_3280_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3271_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3271_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
}
}
else
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
lean_dec(v_traceMsgs_3251_);
lean_dec(v_macroScope_3250_);
lean_dec(v_a_3249_);
v_a_3291_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___x_3254_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3254_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3291_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
}
else
{
lean_object* v_a_3299_; 
v_a_3299_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_a_3299_);
lean_dec_ref_known(v___x_3247_, 2);
if (lean_obj_tag(v_a_3299_) == 0)
{
lean_object* v_a_3300_; lean_object* v_a_3301_; lean_object* v___x_3302_; uint8_t v___x_3303_; 
v_a_3300_ = lean_ctor_get(v_a_3299_, 0);
lean_inc(v_a_3300_);
v_a_3301_ = lean_ctor_get(v_a_3299_, 1);
lean_inc_ref(v_a_3301_);
lean_dec_ref_known(v_a_3299_, 2);
v___x_3302_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___closed__0));
v___x_3303_ = lean_string_dec_eq(v_a_3301_, v___x_3302_);
if (v___x_3303_ == 0)
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3304_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3304_, 0, v_a_3301_);
v___x_3305_ = l_Lean_MessageData_ofFormat(v___x_3304_);
v___x_3306_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_a_3300_, v___x_3305_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
lean_dec(v_a_3300_);
return v___x_3306_;
}
else
{
lean_object* v___x_3307_; 
lean_dec_ref(v_a_3301_);
v___x_3307_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_a_3300_);
return v___x_3307_;
}
}
else
{
lean_object* v___x_3308_; 
v___x_3308_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
return v___x_3308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___boxed(lean_object* v_x_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v_x_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(lean_object* v_pre_3318_, lean_object* v_binders_3319_, lean_object* v_type_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_){
_start:
{
lean_object* v___y_3329_; lean_object* v___f_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_inc_ref(v_pre_3318_);
v___f_3333_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1___boxed), 10, 2);
lean_closure_set(v___f_3333_, 0, v_type_3320_);
lean_closure_set(v___f_3333_, 1, v_pre_3318_);
v___x_3334_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___boxed), 10, 3);
lean_closure_set(v___x_3334_, 0, lean_box(0));
lean_closure_set(v___x_3334_, 1, v_binders_3319_);
lean_closure_set(v___x_3334_, 2, v___f_3333_);
v___x_3335_ = l_Lean_Elab_Term_withAutoBoundImplicit___redArg(v___x_3334_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_dec_ref(v_pre_3318_);
v___y_3329_ = v___x_3335_;
goto v___jp_3328_;
}
else
{
lean_object* v_a_3336_; uint8_t v___y_3338_; uint8_t v___x_3342_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
v___x_3342_ = l_Lean_Exception_isInterrupt(v_a_3336_);
if (v___x_3342_ == 0)
{
uint8_t v___x_3343_; 
v___x_3343_ = l_Lean_Exception_isRuntime(v_a_3336_);
v___y_3338_ = v___x_3343_;
goto v___jp_3337_;
}
else
{
lean_dec(v_a_3336_);
v___y_3338_ = v___x_3342_;
goto v___jp_3337_;
}
v___jp_3337_:
{
if (v___y_3338_ == 0)
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
lean_dec_ref_known(v___x_3335_, 1);
v___x_3339_ = lean_box(0);
v___x_3340_ = l_Lean_Name_str___override(v___x_3339_, v_pre_3318_);
v___x_3341_ = l_Lean_Core_mkFreshUserName(v___x_3340_, v_a_3325_, v_a_3326_);
v___y_3329_ = v___x_3341_;
goto v___jp_3328_;
}
else
{
lean_dec_ref(v_pre_3318_);
v___y_3329_ = v___x_3335_;
goto v___jp_3328_;
}
}
}
v___jp_3328_:
{
if (lean_obj_tag(v___y_3329_) == 0)
{
lean_object* v_a_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v_a_3330_ = lean_ctor_get(v___y_3329_, 0);
lean_inc(v_a_3330_);
lean_dec_ref_known(v___y_3329_, 1);
v___x_3331_ = lean_alloc_closure((void*)(l_Lean_Elab_mkUnusedBaseName___boxed), 3, 1);
lean_closure_set(v___x_3331_, 0, v_a_3330_);
v___x_3332_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v___x_3331_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_);
return v___x_3332_;
}
else
{
return v___y_3329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___boxed(lean_object* v_pre_3344_, lean_object* v_binders_3345_, lean_object* v_type_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(v_pre_3344_, v_binders_3345_, v_type_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
lean_dec(v_a_3352_);
lean_dec_ref(v_a_3351_);
lean_dec(v_a_3350_);
lean_dec_ref(v_a_3349_);
lean_dec(v_a_3348_);
lean_dec_ref(v_a_3347_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2(lean_object* v_00_u03b1_3355_, lean_object* v_x_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v___x_3359_; 
v___x_3359_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v_x_3356_, v___y_3358_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3360_, lean_object* v_x_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2(v_00_u03b1_3360_, v_x_3361_, v___y_3362_, v___y_3363_);
lean_dec_ref(v___y_3362_);
lean_dec_ref(v_x_3361_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7(lean_object* v_00_u03b1_3365_, lean_object* v_ref_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_ref_3366_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___boxed(lean_object* v_00_u03b1_3375_, lean_object* v_ref_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7(v_00_u03b1_3375_, v_ref_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8(lean_object* v_00_u03b1_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v___x_3393_; 
v___x_3393_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
return v___x_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___boxed(lean_object* v_00_u03b1_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8(v_00_u03b1_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1(lean_object* v_00_u03b1_3403_, lean_object* v_x_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v___x_3412_; 
v___x_3412_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v_x_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
return v___x_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___boxed(lean_object* v_00_u03b1_3413_, lean_object* v_x_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1(v_00_u03b1_3413_, v_x_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1(lean_object* v_cls_3423_, lean_object* v_msg_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
lean_object* v___x_3432_; 
v___x_3432_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_3423_, v_msg_3424_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
return v___x_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___boxed(lean_object* v_cls_3433_, lean_object* v_msg_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1(v_cls_3433_, v_msg_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4(lean_object* v_as_3443_, lean_object* v_as_x27_3444_, lean_object* v_b_3445_, lean_object* v_a_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
lean_object* v___x_3454_; 
v___x_3454_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_as_x27_3444_, v_b_3445_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
return v___x_3454_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___boxed(lean_object* v_as_3455_, lean_object* v_as_x27_3456_, lean_object* v_b_3457_, lean_object* v_a_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_){
_start:
{
lean_object* v_res_3466_; 
v_res_3466_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4(v_as_3455_, v_as_x27_3456_, v_b_3457_, v_a_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec(v_as_x27_3456_);
lean_dec(v_as_3455_);
return v_res_3466_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6(lean_object* v_00_u03b1_3467_, lean_object* v_ref_3468_, lean_object* v_msg_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
lean_object* v___x_3477_; 
v___x_3477_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_ref_3468_, v_msg_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
return v___x_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3478_, lean_object* v_ref_3479_, lean_object* v_msg_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6(v_00_u03b1_3478_, v_ref_3479_, v_msg_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v_ref_3479_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_3489_, lean_object* v_m_3490_, lean_object* v_a_3491_){
_start:
{
lean_object* v___x_3492_; 
v___x_3492_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(v_m_3490_, v_a_3491_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3493_, lean_object* v_m_3494_, lean_object* v_a_3495_){
_start:
{
lean_object* v_res_3496_; 
v_res_3496_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6(v_00_u03b2_3493_, v_m_3494_, v_a_3495_);
lean_dec(v_a_3495_);
lean_dec_ref(v_m_3494_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10(lean_object* v_00_u03b1_3497_, lean_object* v_msg_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v___x_3506_; 
v___x_3506_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___boxed(lean_object* v_00_u03b1_3507_, lean_object* v_msg_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10(v_00_u03b1_3507_, v_msg_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
return v_res_3516_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_3517_, lean_object* v_x_3518_, lean_object* v_x_3519_){
_start:
{
uint8_t v___x_3520_; 
v___x_3520_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v_x_3518_, v_x_3519_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3521_, lean_object* v_x_3522_, lean_object* v_x_3523_){
_start:
{
uint8_t v_res_3524_; lean_object* v_r_3525_; 
v_res_3524_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7(v_00_u03b2_3521_, v_x_3522_, v_x_3523_);
lean_dec_ref(v_x_3523_);
lean_dec_ref(v_x_3522_);
v_r_3525_ = lean_box(v_res_3524_);
return v_r_3525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_3526_, lean_object* v_m_3527_, lean_object* v_query_3528_){
_start:
{
lean_object* v___x_3529_; 
v___x_3529_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(v_m_3527_, v_query_3528_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_3530_, lean_object* v_m_3531_, lean_object* v_query_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_3530_, v_m_3531_, v_query_3532_);
lean_dec(v_query_3532_);
lean_dec_ref(v_m_3531_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15(lean_object* v_msgData_3534_, lean_object* v_macroStack_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_){
_start:
{
lean_object* v___x_3543_; 
v___x_3543_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_msgData_3534_, v_macroStack_3535_, v___y_3540_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___boxed(lean_object* v_msgData_3544_, lean_object* v_macroStack_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15(v_msgData_3544_, v_macroStack_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
return v_res_3553_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_3554_, lean_object* v_x_3555_, size_t v_x_3556_, lean_object* v_x_3557_){
_start:
{
uint8_t v___x_3558_; 
v___x_3558_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_3555_, v_x_3556_, v_x_3557_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3559_, lean_object* v_x_3560_, lean_object* v_x_3561_, lean_object* v_x_3562_){
_start:
{
size_t v_x_16196__boxed_3563_; uint8_t v_res_3564_; lean_object* v_r_3565_; 
v_x_16196__boxed_3563_ = lean_unbox_usize(v_x_3561_);
lean_dec(v_x_3561_);
v_res_3564_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11(v_00_u03b2_3559_, v_x_3560_, v_x_16196__boxed_3563_, v_x_3562_);
lean_dec_ref(v_x_3562_);
lean_dec_ref(v_x_3560_);
v_r_3565_ = lean_box(v_res_3564_);
return v_r_3565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15(lean_object* v_00_u03b2_3566_, lean_object* v_m_3567_, lean_object* v_query_3568_){
_start:
{
lean_object* v___x_3569_; 
v___x_3569_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15___redArg(v_m_3567_, v_query_3568_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15___boxed(lean_object* v_00_u03b2_3570_, lean_object* v_m_3571_, lean_object* v_query_3572_){
_start:
{
lean_object* v_res_3573_; 
v_res_3573_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15(v_00_u03b2_3570_, v_m_3571_, v_query_3572_);
lean_dec(v_query_3572_);
lean_dec_ref(v_m_3571_);
return v_res_3573_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15(lean_object* v_00_u03b2_3574_, lean_object* v_keys_3575_, lean_object* v_vals_3576_, lean_object* v_heq_3577_, lean_object* v_i_3578_, lean_object* v_k_3579_){
_start:
{
uint8_t v___x_3580_; 
v___x_3580_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_keys_3575_, v_i_3578_, v_k_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___boxed(lean_object* v_00_u03b2_3581_, lean_object* v_keys_3582_, lean_object* v_vals_3583_, lean_object* v_heq_3584_, lean_object* v_i_3585_, lean_object* v_k_3586_){
_start:
{
uint8_t v_res_3587_; lean_object* v_r_3588_; 
v_res_3587_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15(v_00_u03b2_3581_, v_keys_3582_, v_vals_3583_, v_heq_3584_, v_i_3585_, v_k_3586_);
lean_dec_ref(v_k_3586_);
lean_dec_ref(v_vals_3583_);
lean_dec_ref(v_keys_3582_);
v_r_3588_ = lean_box(v_res_3587_);
return v_r_3588_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15_spec__18(lean_object* v_00_u03b2_3589_, lean_object* v_m_3590_, lean_object* v_query_3591_, lean_object* v_x_3592_, lean_object* v_x_3593_, lean_object* v_x_3594_, lean_object* v_x_3595_){
_start:
{
lean_object* v___x_3596_; 
v___x_3596_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15_spec__18___redArg(v_m_3590_, v_query_3591_, v_x_3592_, v_x_3593_, v_x_3594_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15_spec__18___boxed(lean_object* v_00_u03b2_3597_, lean_object* v_m_3598_, lean_object* v_query_3599_, lean_object* v_x_3600_, lean_object* v_x_3601_, lean_object* v_x_3602_, lean_object* v_x_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10_spec__15_spec__18(v_00_u03b2_3597_, v_m_3598_, v_query_3599_, v_x_3600_, v_x_3601_, v_x_3602_, v_x_3603_);
lean_dec(v_query_3599_);
lean_dec_ref(v_m_3598_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__0(lean_object* v_binders_3606_, lean_object* v_type_3607_, lean_object* v_x_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3616_ = ((lean_object*)(l_Lean_Elab_Command_mkInstanceName___lam__0___closed__0));
v___x_3617_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(v___x_3616_, v_binders_3606_, v_type_3607_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__0___boxed(lean_object* v_binders_3618_, lean_object* v_type_3619_, lean_object* v_x_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_Elab_Command_mkInstanceName___lam__0(v_binders_3618_, v_type_3619_, v_x_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec_ref(v_x_3620_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__1(lean_object* v_a_3629_, lean_object* v_val_3630_, lean_object* v_a_x3f_3631_){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3633_ = lean_st_ref_swap(v_a_3629_, v_val_3630_);
lean_dec(v___x_3633_);
v___x_3634_ = lean_box(0);
v___x_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3634_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__1___boxed(lean_object* v_a_3636_, lean_object* v_val_3637_, lean_object* v_a_x3f_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l_Lean_Elab_Command_mkInstanceName___lam__1(v_a_3636_, v_val_3637_, v_a_x3f_3638_);
lean_dec(v_a_x3f_3638_);
lean_dec(v_a_3636_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName(lean_object* v_binders_3641_, lean_object* v_type_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_){
_start:
{
lean_object* v___x_3646_; lean_object* v___f_3647_; lean_object* v_r_3648_; 
v___x_3646_ = lean_st_ref_get(v_a_3644_);
v___f_3647_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkInstanceName___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3647_, 0, v_binders_3641_);
lean_closure_set(v___f_3647_, 1, v_type_3642_);
v_r_3648_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_3647_, v_a_3643_, v_a_3644_);
if (lean_obj_tag(v_r_3648_) == 0)
{
lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3665_; 
v_a_3649_ = lean_ctor_get(v_r_3648_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v_r_3648_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3651_ = v_r_3648_;
v_isShared_3652_ = v_isSharedCheck_3665_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v_r_3648_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3665_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3654_; 
lean_inc(v_a_3649_);
if (v_isShared_3652_ == 0)
{
lean_ctor_set_tag(v___x_3651_, 1);
v___x_3654_ = v___x_3651_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3649_);
v___x_3654_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
v___x_3655_ = l_Lean_Elab_Command_mkInstanceName___lam__1(v_a_3644_, v___x_3646_, v___x_3654_);
lean_dec_ref(v___x_3654_);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3662_ == 0)
{
lean_object* v_unused_3663_; 
v_unused_3663_ = lean_ctor_get(v___x_3655_, 0);
lean_dec(v_unused_3663_);
v___x_3657_ = v___x_3655_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_dec(v___x_3655_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3660_; 
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 0, v_a_3649_);
v___x_3660_ = v___x_3657_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3649_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
}
}
else
{
lean_object* v_a_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
v_a_3666_ = lean_ctor_get(v_r_3648_, 0);
lean_inc(v_a_3666_);
lean_dec_ref_known(v_r_3648_, 1);
v___x_3667_ = lean_box(0);
v___x_3668_ = l_Lean_Elab_Command_mkInstanceName___lam__1(v_a_3644_, v___x_3646_, v___x_3667_);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3675_ == 0)
{
lean_object* v_unused_3676_; 
v_unused_3676_ = lean_ctor_get(v___x_3668_, 0);
lean_dec(v_unused_3676_);
v___x_3670_ = v___x_3668_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_dec(v___x_3668_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
lean_ctor_set_tag(v___x_3670_, 1);
lean_ctor_set(v___x_3670_, 0, v_a_3666_);
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3666_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___boxed(lean_object* v_binders_3677_, lean_object* v_type_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l_Lean_Elab_Command_mkInstanceName(v_binders_3677_, v_type_3678_, v_a_3679_, v_a_3680_);
lean_dec(v_a_3680_);
lean_dec_ref(v_a_3679_);
return v_res_3682_;
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
