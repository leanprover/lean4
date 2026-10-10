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
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__27;
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
lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg(lean_object* v_e_1_, lean_object* v_a_2_){
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
LEAN_EXPORT void l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_res_61_;
v_res_61_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg(v_e_1_, v_a_2_);
stack->m_obj
 = v_res_61_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg___boxed(lean_object* v_e_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg(v_e_62_, v_a_63_);
lean_dec(v_a_63_);
lean_dec_ref(v_e_62_);
return v_res_65_;
}
}
lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg(lean_object* v_e_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg(v_e_66_, v_a_70_);
return v___x_72_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_66_ = stack[0].m_obj;
lean_object* v_a_67_ = stack[1].m_obj;
lean_object* v_a_68_ = stack[2].m_obj;
lean_object* v_a_69_ = stack[3].m_obj;
lean_object* v_a_70_ = stack[4].m_obj;
lean_object* v_res_73_;
v_res_73_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg(v_e_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___boxed(lean_object* v_e_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg(v_e_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_);
lean_dec(v_a_78_);
lean_dec_ref(v_a_77_);
lean_dec(v_a_76_);
lean_dec_ref(v_a_75_);
lean_dec_ref(v_e_74_);
return v_res_80_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___lam__0(lean_object* v_k_81_, lean_object* v___y_82_, lean_object* v_b_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v___x_89_; 
lean_inc(v___y_87_);
lean_inc_ref(v___y_86_);
lean_inc(v___y_85_);
lean_inc_ref(v___y_84_);
lean_inc(v___y_82_);
v___x_89_ = lean_apply_7(v_k_81_, v_b_83_, v___y_82_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, lean_box(0));
return v___x_89_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_81_ = stack[0].m_obj;
lean_object* v___y_82_ = stack[1].m_obj;
lean_object* v_b_83_ = stack[2].m_obj;
lean_object* v___y_84_ = stack[3].m_obj;
lean_object* v___y_85_ = stack[4].m_obj;
lean_object* v___y_86_ = stack[5].m_obj;
lean_object* v___y_87_ = stack[6].m_obj;
lean_object* v_res_90_;
v_res_90_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___lam__0(v_k_81_, v___y_82_, v_b_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
stack->m_obj
 = v_res_90_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___lam__0___boxed(lean_object* v_k_91_, lean_object* v___y_92_, lean_object* v_b_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___lam__0(v_k_91_, v___y_92_, v_b_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_92_);
return v_res_99_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(lean_object* v_name_100_, uint8_t v_bi_101_, lean_object* v_type_102_, lean_object* v_k_103_, uint8_t v_kind_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v___f_111_; lean_object* v___x_112_; 
lean_inc(v___y_105_);
v___f_111_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_111_, 0, v_k_103_);
lean_closure_set(v___f_111_, 1, v___y_105_);
v___x_112_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_100_, v_bi_101_, v_type_102_, v___f_111_, v_kind_104_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
if (lean_obj_tag(v___x_112_) == 0)
{
return v___x_112_;
}
else
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_120_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_120_ == 0)
{
v___x_115_ = v___x_112_;
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_112_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_113_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_100_ = stack[0].m_obj;
uint8_t v_bi_101_ = stack[1].m_num;
lean_object* v_type_102_ = stack[2].m_obj;
lean_object* v_k_103_ = stack[3].m_obj;
uint8_t v_kind_104_ = stack[4].m_num;
lean_object* v___y_105_ = stack[5].m_obj;
lean_object* v___y_106_ = stack[6].m_obj;
lean_object* v___y_107_ = stack[7].m_obj;
lean_object* v___y_108_ = stack[8].m_obj;
lean_object* v___y_109_ = stack[9].m_obj;
lean_object* v_res_121_;
v_res_121_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(v_name_100_, v_bi_101_, v_type_102_, v_k_103_, v_kind_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
stack->m_obj
 = v_res_121_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___boxed(lean_object* v_name_122_, lean_object* v_bi_123_, lean_object* v_type_124_, lean_object* v_k_125_, lean_object* v_kind_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
uint8_t v_bi_boxed_133_; uint8_t v_kind_boxed_134_; lean_object* v_res_135_; 
v_bi_boxed_133_ = lean_unbox(v_bi_123_);
v_kind_boxed_134_ = lean_unbox(v_kind_126_);
v_res_135_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(v_name_122_, v_bi_boxed_133_, v_type_124_, v_k_125_, v_kind_boxed_134_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
return v_res_135_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5(lean_object* v_00_u03b1_136_, lean_object* v_name_137_, uint8_t v_bi_138_, lean_object* v_type_139_, lean_object* v_k_140_, uint8_t v_kind_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(v_name_137_, v_bi_138_, v_type_139_, v_k_140_, v_kind_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
return v___x_148_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_137_ = stack[1].m_obj;
uint8_t v_bi_138_ = stack[2].m_num;
lean_object* v_type_139_ = stack[3].m_obj;
lean_object* v_k_140_ = stack[4].m_obj;
uint8_t v_kind_141_ = stack[5].m_num;
lean_object* v___y_142_ = stack[6].m_obj;
lean_object* v___y_143_ = stack[7].m_obj;
lean_object* v___y_144_ = stack[8].m_obj;
lean_object* v___y_145_ = stack[9].m_obj;
lean_object* v___y_146_ = stack[10].m_obj;
lean_object* v_res_149_;
v_res_149_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5(lean_box(0), v_name_137_, v_bi_138_, v_type_139_, v_k_140_, v_kind_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
stack->m_obj
 = v_res_149_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___boxed(lean_object* v_00_u03b1_150_, lean_object* v_name_151_, lean_object* v_bi_152_, lean_object* v_type_153_, lean_object* v_k_154_, lean_object* v_kind_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
uint8_t v_bi_boxed_162_; uint8_t v_kind_boxed_163_; lean_object* v_res_164_; 
v_bi_boxed_162_ = lean_unbox(v_bi_152_);
v_kind_boxed_163_ = lean_unbox(v_kind_155_);
v_res_164_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5(v_00_u03b1_150_, v_name_151_, v_bi_boxed_162_, v_type_153_, v_k_154_, v_kind_boxed_163_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec(v___y_156_);
return v_res_164_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(lean_object* v_msgData_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v___x_171_; lean_object* v_env_172_; uint8_t v___x_173_; lean_object* v_env_174_; lean_object* v___x_175_; lean_object* v_toCold_176_; lean_object* v_mctx_177_; lean_object* v_lctx_178_; lean_object* v_options_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_171_ = lean_st_ref_get(v___y_169_);
v_env_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc_ref(v_env_172_);
lean_dec(v___x_171_);
v___x_173_ = 0;
v_env_174_ = l_Lean_Environment_setRecordingDeps(v_env_172_, v___x_173_);
v___x_175_ = lean_st_ref_get(v___y_167_);
v_toCold_176_ = lean_ctor_get(v___y_168_, 0);
v_mctx_177_ = lean_ctor_get(v___x_175_, 0);
lean_inc_ref(v_mctx_177_);
lean_dec(v___x_175_);
v_lctx_178_ = lean_ctor_get(v___y_166_, 2);
v_options_179_ = lean_ctor_get(v_toCold_176_, 2);
lean_inc_ref(v_options_179_);
lean_inc_ref(v_lctx_178_);
v___x_180_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_180_, 0, v_env_174_);
lean_ctor_set(v___x_180_, 1, v_mctx_177_);
lean_ctor_set(v___x_180_, 2, v_lctx_178_);
lean_ctor_set(v___x_180_, 3, v_options_179_);
v___x_181_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v_msgData_165_);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_165_ = stack[0].m_obj;
lean_object* v___y_166_ = stack[1].m_obj;
lean_object* v___y_167_ = stack[2].m_obj;
lean_object* v___y_168_ = stack[3].m_obj;
lean_object* v___y_169_ = stack[4].m_obj;
lean_object* v_res_183_;
v_res_183_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msgData_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
stack->m_obj
 = v_res_183_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0___boxed(lean_object* v_msgData_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msgData_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
return v_res_190_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(lean_object* v_msg_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_ref_197_; lean_object* v___x_198_; lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_207_; 
v_ref_197_ = lean_ctor_get(v___y_194_, 2);
v___x_198_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msg_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
v_a_199_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_207_ == 0)
{
v___x_201_ = v___x_198_;
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_198_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___x_205_; 
lean_inc(v_ref_197_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v_ref_197_);
lean_ctor_set(v___x_203_, 1, v_a_199_);
if (v_isShared_202_ == 0)
{
lean_ctor_set_tag(v___x_201_, 1);
lean_ctor_set(v___x_201_, 0, v___x_203_);
v___x_205_ = v___x_201_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_191_ = stack[0].m_obj;
lean_object* v___y_192_ = stack[1].m_obj;
lean_object* v___y_193_ = stack[2].m_obj;
lean_object* v___y_194_ = stack[3].m_obj;
lean_object* v___y_195_ = stack[4].m_obj;
lean_object* v_res_208_;
v_res_208_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v_msg_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
stack->m_obj
 = v_res_208_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg___boxed(lean_object* v_msg_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v_msg_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
return v_res_215_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(lean_object* v_a_216_, lean_object* v_x_217_){
_start:
{
if (lean_obj_tag(v_x_217_) == 0)
{
uint8_t v___x_218_; 
v___x_218_ = 0;
return v___x_218_;
}
else
{
lean_object* v_key_219_; lean_object* v_tail_220_; uint8_t v___x_221_; 
v_key_219_ = lean_ctor_get(v_x_217_, 0);
v_tail_220_ = lean_ctor_get(v_x_217_, 2);
v___x_221_ = lean_expr_eqv(v_key_219_, v_a_216_);
if (v___x_221_ == 0)
{
v_x_217_ = v_tail_220_;
goto _start;
}
else
{
return v___x_221_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_216_ = stack[0].m_obj;
lean_object* v_x_217_ = stack[1].m_obj;
uint8_t v_res_223_;
v_res_223_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_216_, v_x_217_);
stack->m_num = v_res_223_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg___boxed(lean_object* v_a_224_, lean_object* v_x_225_){
_start:
{
uint8_t v_res_226_; lean_object* v_r_227_; 
v_res_226_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_224_, v_x_225_);
lean_dec(v_x_225_);
lean_dec_ref(v_a_224_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9___redArg(lean_object* v_x_228_, lean_object* v_x_229_){
_start:
{
if (lean_obj_tag(v_x_229_) == 0)
{
return v_x_228_;
}
else
{
lean_object* v_key_230_; lean_object* v_value_231_; lean_object* v_tail_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_255_; 
v_key_230_ = lean_ctor_get(v_x_229_, 0);
v_value_231_ = lean_ctor_get(v_x_229_, 1);
v_tail_232_ = lean_ctor_get(v_x_229_, 2);
v_isSharedCheck_255_ = !lean_is_exclusive(v_x_229_);
if (v_isSharedCheck_255_ == 0)
{
v___x_234_ = v_x_229_;
v_isShared_235_ = v_isSharedCheck_255_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_tail_232_);
lean_inc(v_value_231_);
lean_inc(v_key_230_);
lean_dec(v_x_229_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_255_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; uint64_t v_fold_240_; uint64_t v___x_241_; uint64_t v___x_242_; uint64_t v___x_243_; size_t v___x_244_; size_t v___x_245_; size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_236_ = lean_array_get_size(v_x_228_);
v___x_237_ = l_Lean_Expr_hash(v_key_230_);
v___x_238_ = 32ULL;
v___x_239_ = lean_uint64_shift_right(v___x_237_, v___x_238_);
v_fold_240_ = lean_uint64_xor(v___x_237_, v___x_239_);
v___x_241_ = 16ULL;
v___x_242_ = lean_uint64_shift_right(v_fold_240_, v___x_241_);
v___x_243_ = lean_uint64_xor(v_fold_240_, v___x_242_);
v___x_244_ = lean_uint64_to_usize(v___x_243_);
v___x_245_ = lean_usize_of_nat(v___x_236_);
v___x_246_ = ((size_t)1ULL);
v___x_247_ = lean_usize_sub(v___x_245_, v___x_246_);
v___x_248_ = lean_usize_land(v___x_244_, v___x_247_);
v___x_249_ = lean_array_uget_borrowed(v_x_228_, v___x_248_);
lean_inc(v___x_249_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 2, v___x_249_);
v___x_251_ = v___x_234_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_key_230_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_value_231_);
lean_ctor_set(v_reuseFailAlloc_254_, 2, v___x_249_);
v___x_251_ = v_reuseFailAlloc_254_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; 
v___x_252_ = lean_array_uset(v_x_228_, v___x_248_, v___x_251_);
v_x_228_ = v___x_252_;
v_x_229_ = v_tail_232_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6___redArg(lean_object* v_i_256_, lean_object* v_source_257_, lean_object* v_target_258_){
_start:
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = lean_array_get_size(v_source_257_);
v___x_260_ = lean_nat_dec_lt(v_i_256_, v___x_259_);
if (v___x_260_ == 0)
{
lean_dec_ref(v_source_257_);
lean_dec(v_i_256_);
return v_target_258_;
}
else
{
lean_object* v_es_261_; lean_object* v___x_262_; lean_object* v_source_263_; lean_object* v_target_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_es_261_ = lean_array_fget(v_source_257_, v_i_256_);
v___x_262_ = lean_box(0);
v_source_263_ = lean_array_fset(v_source_257_, v_i_256_, v___x_262_);
v_target_264_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9___redArg(v_target_258_, v_es_261_);
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_nat_add(v_i_256_, v___x_265_);
lean_dec(v_i_256_);
v_i_256_ = v___x_266_;
v_source_257_ = v_source_263_;
v_target_258_ = v_target_264_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(lean_object* v_data_268_){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v_nbuckets_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_269_ = lean_array_get_size(v_data_268_);
v___x_270_ = lean_unsigned_to_nat(2u);
v_nbuckets_271_ = lean_nat_mul(v___x_269_, v___x_270_);
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_box(0);
v___x_274_ = lean_mk_array(v_nbuckets_271_, v___x_273_);
v___x_275_ = lean_array_propagate_mark(v_data_268_, v___x_274_);
v___x_276_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6___redArg(v___x_272_, v_data_268_, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(lean_object* v_a_277_, lean_object* v_b_278_, lean_object* v_x_279_){
_start:
{
if (lean_obj_tag(v_x_279_) == 0)
{
lean_dec(v_b_278_);
lean_dec_ref(v_a_277_);
return v_x_279_;
}
else
{
lean_object* v_key_280_; lean_object* v_value_281_; lean_object* v_tail_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_294_; 
v_key_280_ = lean_ctor_get(v_x_279_, 0);
v_value_281_ = lean_ctor_get(v_x_279_, 1);
v_tail_282_ = lean_ctor_get(v_x_279_, 2);
v_isSharedCheck_294_ = !lean_is_exclusive(v_x_279_);
if (v_isSharedCheck_294_ == 0)
{
v___x_284_ = v_x_279_;
v_isShared_285_ = v_isSharedCheck_294_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_tail_282_);
lean_inc(v_value_281_);
lean_inc(v_key_280_);
lean_dec(v_x_279_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_294_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
uint8_t v___x_286_; 
v___x_286_ = lean_expr_eqv(v_key_280_, v_a_277_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_287_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(v_a_277_, v_b_278_, v_tail_282_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 2, v___x_287_);
v___x_289_ = v___x_284_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_key_280_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_value_281_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v___x_287_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
else
{
lean_object* v___x_292_; 
lean_dec(v_value_281_);
lean_dec(v_key_280_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 1, v_b_278_);
lean_ctor_set(v___x_284_, 0, v_a_277_);
v___x_292_ = v___x_284_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_277_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_b_278_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_tail_282_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(lean_object* v_m_295_, lean_object* v_a_296_, lean_object* v_b_297_){
_start:
{
lean_object* v_size_298_; lean_object* v_buckets_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_342_; 
v_size_298_ = lean_ctor_get(v_m_295_, 0);
v_buckets_299_ = lean_ctor_get(v_m_295_, 1);
v_isSharedCheck_342_ = !lean_is_exclusive(v_m_295_);
if (v_isSharedCheck_342_ == 0)
{
v___x_301_ = v_m_295_;
v_isShared_302_ = v_isSharedCheck_342_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_buckets_299_);
lean_inc(v_size_298_);
lean_dec(v_m_295_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_342_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; uint64_t v___x_304_; uint64_t v___x_305_; uint64_t v___x_306_; uint64_t v_fold_307_; uint64_t v___x_308_; uint64_t v___x_309_; uint64_t v___x_310_; size_t v___x_311_; size_t v___x_312_; size_t v___x_313_; size_t v___x_314_; size_t v___x_315_; lean_object* v_bkt_316_; uint8_t v___x_317_; 
v___x_303_ = lean_array_get_size(v_buckets_299_);
v___x_304_ = l_Lean_Expr_hash(v_a_296_);
v___x_305_ = 32ULL;
v___x_306_ = lean_uint64_shift_right(v___x_304_, v___x_305_);
v_fold_307_ = lean_uint64_xor(v___x_304_, v___x_306_);
v___x_308_ = 16ULL;
v___x_309_ = lean_uint64_shift_right(v_fold_307_, v___x_308_);
v___x_310_ = lean_uint64_xor(v_fold_307_, v___x_309_);
v___x_311_ = lean_uint64_to_usize(v___x_310_);
v___x_312_ = lean_usize_of_nat(v___x_303_);
v___x_313_ = ((size_t)1ULL);
v___x_314_ = lean_usize_sub(v___x_312_, v___x_313_);
v___x_315_ = lean_usize_land(v___x_311_, v___x_314_);
v_bkt_316_ = lean_array_uget_borrowed(v_buckets_299_, v___x_315_);
v___x_317_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_296_, v_bkt_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v_size_x27_319_; lean_object* v___x_320_; lean_object* v_buckets_x27_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_318_ = lean_unsigned_to_nat(1u);
v_size_x27_319_ = lean_nat_add(v_size_298_, v___x_318_);
lean_dec(v_size_298_);
lean_inc(v_bkt_316_);
v___x_320_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_320_, 0, v_a_296_);
lean_ctor_set(v___x_320_, 1, v_b_297_);
lean_ctor_set(v___x_320_, 2, v_bkt_316_);
v_buckets_x27_321_ = lean_array_uset(v_buckets_299_, v___x_315_, v___x_320_);
v___x_322_ = lean_unsigned_to_nat(4u);
v___x_323_ = lean_nat_mul(v_size_x27_319_, v___x_322_);
v___x_324_ = lean_unsigned_to_nat(3u);
v___x_325_ = lean_nat_div(v___x_323_, v___x_324_);
lean_dec(v___x_323_);
v___x_326_ = lean_array_get_size(v_buckets_x27_321_);
v___x_327_ = lean_nat_dec_le(v___x_325_, v___x_326_);
lean_dec(v___x_325_);
if (v___x_327_ == 0)
{
lean_object* v_val_328_; lean_object* v___x_330_; 
v_val_328_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(v_buckets_x27_321_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v_val_328_);
lean_ctor_set(v___x_301_, 0, v_size_x27_319_);
v___x_330_ = v___x_301_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_size_x27_319_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_val_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
else
{
lean_object* v___x_333_; 
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v_buckets_x27_321_);
lean_ctor_set(v___x_301_, 0, v_size_x27_319_);
v___x_333_ = v___x_301_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_size_x27_319_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_buckets_x27_321_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
else
{
lean_object* v___x_335_; lean_object* v_buckets_x27_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_340_; 
lean_inc(v_bkt_316_);
v___x_335_ = lean_box(0);
v_buckets_x27_336_ = lean_array_uset(v_buckets_299_, v___x_315_, v___x_335_);
v___x_337_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(v_a_296_, v_b_297_, v_bkt_316_);
v___x_338_ = lean_array_uset(v_buckets_x27_336_, v___x_315_, v___x_337_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v___x_338_);
v___x_340_ = v___x_301_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_size_298_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(lean_object* v_a_343_, lean_object* v_x_344_){
_start:
{
if (lean_obj_tag(v_x_344_) == 0)
{
lean_object* v___x_345_; 
v___x_345_ = lean_box(0);
return v___x_345_;
}
else
{
lean_object* v_key_346_; lean_object* v_value_347_; lean_object* v_tail_348_; uint8_t v___x_349_; 
v_key_346_ = lean_ctor_get(v_x_344_, 0);
v_value_347_ = lean_ctor_get(v_x_344_, 1);
v_tail_348_ = lean_ctor_get(v_x_344_, 2);
v___x_349_ = lean_expr_eqv(v_key_346_, v_a_343_);
if (v___x_349_ == 0)
{
v_x_344_ = v_tail_348_;
goto _start;
}
else
{
lean_object* v___x_351_; 
lean_inc(v_value_347_);
v___x_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_351_, 0, v_value_347_);
return v___x_351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg___boxed(lean_object* v_a_352_, lean_object* v_x_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(v_a_352_, v_x_353_);
lean_dec(v_x_353_);
lean_dec_ref(v_a_352_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(lean_object* v_m_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_buckets_357_; lean_object* v___x_358_; uint64_t v___x_359_; uint64_t v___x_360_; uint64_t v___x_361_; uint64_t v_fold_362_; uint64_t v___x_363_; uint64_t v___x_364_; uint64_t v___x_365_; size_t v___x_366_; size_t v___x_367_; size_t v___x_368_; size_t v___x_369_; size_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_buckets_357_ = lean_ctor_get(v_m_355_, 1);
v___x_358_ = lean_array_get_size(v_buckets_357_);
v___x_359_ = l_Lean_Expr_hash(v_a_356_);
v___x_360_ = 32ULL;
v___x_361_ = lean_uint64_shift_right(v___x_359_, v___x_360_);
v_fold_362_ = lean_uint64_xor(v___x_359_, v___x_361_);
v___x_363_ = 16ULL;
v___x_364_ = lean_uint64_shift_right(v_fold_362_, v___x_363_);
v___x_365_ = lean_uint64_xor(v_fold_362_, v___x_364_);
v___x_366_ = lean_uint64_to_usize(v___x_365_);
v___x_367_ = lean_usize_of_nat(v___x_358_);
v___x_368_ = ((size_t)1ULL);
v___x_369_ = lean_usize_sub(v___x_367_, v___x_368_);
v___x_370_ = lean_usize_land(v___x_366_, v___x_369_);
v___x_371_ = lean_array_uget_borrowed(v_buckets_357_, v___x_370_);
v___x_372_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(v_a_356_, v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg___boxed(lean_object* v_m_373_, lean_object* v_a_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v_m_373_, v_a_374_);
lean_dec_ref(v_a_374_);
lean_dec_ref(v_m_373_);
return v_res_375_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0(void){
_start:
{
lean_object* v___x_376_; lean_object* v_dummy_377_; 
v___x_376_ = lean_box(0);
v_dummy_377_ = l_Lean_Expr_sort___override(v___x_376_);
return v_dummy_377_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__0));
v___x_380_ = l_Lean_stringToMessageData(v___x_379_);
return v___x_380_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(lean_object* v_snd_381_, lean_object* v_args_382_, lean_object* v_a_383_, lean_object* v_____r_384_, lean_object* v_fty_385_, lean_object* v_j_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
if (lean_obj_tag(v_fty_385_) == 7)
{
lean_object* v_body_393_; uint8_t v_binderInfo_394_; lean_object* v___x_400_; uint8_t v_a_402_; uint8_t v___x_445_; 
v_body_393_ = lean_ctor_get(v_fty_385_, 2);
lean_inc_ref(v_body_393_);
v_binderInfo_394_ = lean_ctor_get_uint8(v_fty_385_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_fty_385_, 3);
v___x_400_ = lean_array_fget_borrowed(v_args_382_, v_a_383_);
v___x_445_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_394_);
if (v___x_445_ == 0)
{
uint8_t v___x_446_; 
v___x_446_ = l_Lean_Expr_isSort(v___x_400_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; 
lean_inc(v___x_400_);
v___x_447_ = l_Lean_Meta_isTypeFormer(v___x_400_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; uint8_t v___x_449_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v___x_447_, 1);
v___x_449_ = lean_unbox(v_a_448_);
lean_dec(v_a_448_);
v_a_402_ = v___x_449_;
goto v___jp_401_;
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_dec_ref(v_body_393_);
lean_dec(v_snd_381_);
v_a_450_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_447_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_447_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
else
{
goto v___jp_395_;
}
}
else
{
v_a_402_ = v___x_445_;
goto v___jp_401_;
}
v___jp_395_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
lean_inc(v_j_386_);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v_j_386_);
lean_ctor_set(v___x_396_, 1, v_snd_381_);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v_body_393_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
v___jp_401_:
{
if (v_a_402_ == 0)
{
goto v___jp_395_;
}
else
{
lean_object* v___x_403_; 
lean_inc(v___x_400_);
v___x_403_ = l_Lean_Meta_isProof(v___x_400_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_436_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_436_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_436_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_436_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
uint8_t v___x_408_; 
v___x_408_ = lean_unbox(v_a_404_);
lean_dec(v_a_404_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; 
lean_del_object(v___x_406_);
lean_inc(v___x_400_);
v___x_409_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_400_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_421_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_421_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_421_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_421_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_414_ = l_Lean_Expr_app___override(v_snd_381_, v_a_410_);
lean_inc(v_j_386_);
v___x_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_415_, 0, v_j_386_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v_body_393_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_417_);
v___x_419_ = v___x_412_;
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
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec_ref(v_body_393_);
lean_dec(v_snd_381_);
v_a_422_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_409_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_409_);
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
else
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_434_; 
lean_inc(v_j_386_);
v___x_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_430_, 0, v_j_386_);
lean_ctor_set(v___x_430_, 1, v_snd_381_);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v_body_393_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
v___x_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v___x_432_);
v___x_434_ = v___x_406_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
lean_dec_ref(v_body_393_);
lean_dec(v_snd_381_);
v_a_437_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_403_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_403_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1);
v___x_459_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v___x_458_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_469_; 
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; 
v_unused_470_ = lean_ctor_get(v___x_459_, 0);
lean_dec(v_unused_470_);
v___x_461_ = v___x_459_;
v_isShared_462_ = v_isSharedCheck_469_;
goto v_resetjp_460_;
}
else
{
lean_dec(v___x_459_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_469_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
lean_inc(v_j_386_);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v_j_386_);
lean_ctor_set(v___x_463_, 1, v_snd_381_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v_fty_385_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_465_);
v___x_467_ = v___x_461_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_dec_ref(v_fty_385_);
lean_dec(v_snd_381_);
v_a_471_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_459_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_459_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_381_ = stack[0].m_obj;
lean_object* v_args_382_ = stack[1].m_obj;
lean_object* v_a_383_ = stack[2].m_obj;
lean_object* v_____r_384_ = stack[3].m_obj;
lean_object* v_fty_385_ = stack[4].m_obj;
lean_object* v_j_386_ = stack[5].m_obj;
lean_object* v___y_387_ = stack[6].m_obj;
lean_object* v___y_388_ = stack[7].m_obj;
lean_object* v___y_389_ = stack[8].m_obj;
lean_object* v___y_390_ = stack[9].m_obj;
lean_object* v___y_391_ = stack[10].m_obj;
lean_object* v_res_479_;
v_res_479_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_snd_381_, v_args_382_, v_a_383_, v_____r_384_, v_fty_385_, v_j_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
stack->m_obj
 = v_res_479_;
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(lean_object* v_upperBound_480_, lean_object* v_args_481_, lean_object* v_a_482_, lean_object* v_b_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v___y_491_; uint8_t v___x_513_; 
v___x_513_ = lean_nat_dec_lt(v_a_482_, v_upperBound_480_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
lean_dec(v_a_482_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v_b_483_);
return v___x_514_;
}
else
{
lean_object* v_snd_515_; lean_object* v_fst_516_; lean_object* v_fst_517_; lean_object* v_snd_518_; lean_object* v___y_520_; uint8_t v___x_532_; 
v_snd_515_ = lean_ctor_get(v_b_483_, 1);
lean_inc(v_snd_515_);
v_fst_516_ = lean_ctor_get(v_b_483_, 0);
lean_inc(v_fst_516_);
lean_dec_ref(v_b_483_);
v_fst_517_ = lean_ctor_get(v_snd_515_, 0);
lean_inc(v_fst_517_);
v_snd_518_ = lean_ctor_get(v_snd_515_, 1);
lean_inc(v_snd_518_);
lean_dec(v_snd_515_);
v___x_532_ = l_Lean_Expr_isForall(v_fst_516_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; uint8_t v_transparency_534_; uint8_t v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_533_ = l_Lean_Meta_Context_config(v___y_485_);
v_transparency_534_ = lean_ctor_get_uint8(v___x_533_, 9);
lean_dec_ref(v___x_533_);
v___x_535_ = 0;
v___x_536_ = lean_expr_instantiate_rev_range(v_fst_516_, v_fst_517_, v_a_482_, v_args_481_);
lean_dec(v_fst_517_);
lean_dec(v_fst_516_);
v___x_537_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_534_, v___x_535_);
if (v___x_537_ == 0)
{
lean_object* v_keyedConfig_538_; uint8_t v_trackZetaDelta_539_; lean_object* v_zetaDeltaSet_540_; lean_object* v_lctx_541_; lean_object* v_localInstances_542_; lean_object* v_defEqCtx_x3f_543_; lean_object* v_synthPendingDepth_544_; lean_object* v_customCanUnfoldPredicate_x3f_545_; uint8_t v_univApprox_546_; uint8_t v_inTypeClassResolution_547_; uint8_t v_cacheInferType_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_keyedConfig_538_ = lean_ctor_get(v___y_485_, 0);
v_trackZetaDelta_539_ = lean_ctor_get_uint8(v___y_485_, sizeof(void*)*7);
v_zetaDeltaSet_540_ = lean_ctor_get(v___y_485_, 1);
v_lctx_541_ = lean_ctor_get(v___y_485_, 2);
v_localInstances_542_ = lean_ctor_get(v___y_485_, 3);
v_defEqCtx_x3f_543_ = lean_ctor_get(v___y_485_, 4);
v_synthPendingDepth_544_ = lean_ctor_get(v___y_485_, 5);
v_customCanUnfoldPredicate_x3f_545_ = lean_ctor_get(v___y_485_, 6);
v_univApprox_546_ = lean_ctor_get_uint8(v___y_485_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_547_ = lean_ctor_get_uint8(v___y_485_, sizeof(void*)*7 + 2);
v_cacheInferType_548_ = lean_ctor_get_uint8(v___y_485_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_538_);
v___x_549_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_535_, v_keyedConfig_538_);
lean_inc(v_customCanUnfoldPredicate_x3f_545_);
lean_inc(v_synthPendingDepth_544_);
lean_inc(v_defEqCtx_x3f_543_);
lean_inc_ref(v_localInstances_542_);
lean_inc_ref(v_lctx_541_);
lean_inc(v_zetaDeltaSet_540_);
v___x_550_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v_zetaDeltaSet_540_);
lean_ctor_set(v___x_550_, 2, v_lctx_541_);
lean_ctor_set(v___x_550_, 3, v_localInstances_542_);
lean_ctor_set(v___x_550_, 4, v_defEqCtx_x3f_543_);
lean_ctor_set(v___x_550_, 5, v_synthPendingDepth_544_);
lean_ctor_set(v___x_550_, 6, v_customCanUnfoldPredicate_x3f_545_);
lean_ctor_set_uint8(v___x_550_, sizeof(void*)*7, v_trackZetaDelta_539_);
lean_ctor_set_uint8(v___x_550_, sizeof(void*)*7 + 1, v_univApprox_546_);
lean_ctor_set_uint8(v___x_550_, sizeof(void*)*7 + 2, v_inTypeClassResolution_547_);
lean_ctor_set_uint8(v___x_550_, sizeof(void*)*7 + 3, v_cacheInferType_548_);
lean_inc(v___y_488_);
lean_inc_ref(v___y_487_);
lean_inc(v___y_486_);
v___x_551_ = lean_whnf(v___x_536_, v___x_550_, v___y_486_, v___y_487_, v___y_488_);
v___y_520_ = v___x_551_;
goto v___jp_519_;
}
else
{
lean_object* v___x_552_; 
lean_inc(v___y_488_);
lean_inc_ref(v___y_487_);
lean_inc(v___y_486_);
lean_inc_ref(v___y_485_);
v___x_552_ = lean_whnf(v___x_536_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
v___y_520_ = v___x_552_;
goto v___jp_519_;
}
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_box(0);
v___x_554_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_snd_518_, v_args_481_, v_a_482_, v___x_553_, v_fst_516_, v_fst_517_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v_fst_517_);
v___y_491_ = v___x_554_;
goto v___jp_490_;
}
v___jp_519_:
{
if (lean_obj_tag(v___y_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_a_521_ = lean_ctor_get(v___y_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref_known(v___y_520_, 1);
v___x_522_ = lean_box(0);
v___x_523_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_snd_518_, v_args_481_, v_a_482_, v___x_522_, v_a_521_, v_a_482_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
v___y_491_ = v___x_523_;
goto v___jp_490_;
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_dec(v_snd_518_);
lean_dec(v_a_482_);
v_a_524_ = lean_ctor_get(v___y_520_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___y_520_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___y_520_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___y_520_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
v___jp_490_:
{
if (lean_obj_tag(v___y_491_) == 0)
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_504_; 
v_a_492_ = lean_ctor_get(v___y_491_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___y_491_);
if (v_isSharedCheck_504_ == 0)
{
v___x_494_ = v___y_491_;
v_isShared_495_ = v_isSharedCheck_504_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___y_491_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_504_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
if (lean_obj_tag(v_a_492_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_498_; 
lean_dec(v_a_482_);
v_a_496_ = lean_ctor_get(v_a_492_, 0);
lean_inc(v_a_496_);
lean_dec_ref_known(v_a_492_, 1);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v_a_496_);
v___x_498_ = v___x_494_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
lean_del_object(v___x_494_);
v_a_500_ = lean_ctor_get(v_a_492_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v_a_492_, 1);
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_add(v_a_482_, v___x_501_);
lean_dec(v_a_482_);
v_a_482_ = v___x_502_;
v_b_483_ = v_a_500_;
goto _start;
}
}
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec(v_a_482_);
v_a_505_ = lean_ctor_get(v___y_491_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___y_491_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___y_491_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___y_491_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_480_ = stack[0].m_obj;
lean_object* v_args_481_ = stack[1].m_obj;
lean_object* v_a_482_ = stack[2].m_obj;
lean_object* v_b_483_ = stack[3].m_obj;
lean_object* v___y_484_ = stack[4].m_obj;
lean_object* v___y_485_ = stack[5].m_obj;
lean_object* v___y_486_ = stack[6].m_obj;
lean_object* v___y_487_ = stack[7].m_obj;
lean_object* v___y_488_ = stack[8].m_obj;
lean_object* v_res_555_;
v_res_555_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v_upperBound_480_, v_args_481_, v_a_482_, v_b_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
stack->m_obj
 = v_res_555_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(lean_object* v_x_556_, lean_object* v_x_557_, lean_object* v_x_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
if (lean_obj_tag(v_x_556_) == 5)
{
lean_object* v_fn_565_; lean_object* v_arg_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v_fn_565_ = lean_ctor_get(v_x_556_, 0);
lean_inc_ref(v_fn_565_);
v_arg_566_ = lean_ctor_get(v_x_556_, 1);
lean_inc_ref(v_arg_566_);
lean_dec_ref_known(v_x_556_, 2);
v___x_567_ = lean_array_set(v_x_557_, v_x_558_, v_arg_566_);
v___x_568_ = lean_unsigned_to_nat(1u);
v___x_569_ = lean_nat_sub(v_x_558_, v___x_568_);
lean_dec(v_x_558_);
v_x_556_ = v_fn_565_;
v_x_557_ = v___x_567_;
v_x_558_ = v___x_569_;
goto _start;
}
else
{
lean_object* v___x_571_; 
lean_dec(v_x_558_);
lean_inc(v___y_563_);
lean_inc_ref(v___y_562_);
lean_inc(v___y_561_);
lean_inc_ref(v___y_560_);
lean_inc_ref(v_x_556_);
v___x_571_ = lean_infer_type(v_x_556_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_571_, 1);
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_x_556_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_574_, 1);
v___x_576_ = lean_array_get_size(v_x_557_);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_573_);
lean_ctor_set(v___x_577_, 1, v_a_575_);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v_a_572_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v___x_576_, v_x_557_, v___x_573_, v___x_578_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec_ref(v_x_557_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_589_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_589_ == 0)
{
v___x_582_ = v___x_579_;
v_isShared_583_ = v_isSharedCheck_589_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_579_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_589_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v_snd_584_; lean_object* v_snd_585_; lean_object* v___x_587_; 
v_snd_584_ = lean_ctor_get(v_a_580_, 1);
lean_inc(v_snd_584_);
lean_dec(v_a_580_);
v_snd_585_ = lean_ctor_get(v_snd_584_, 1);
lean_inc(v_snd_585_);
lean_dec(v_snd_584_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v_snd_585_);
v___x_587_ = v___x_582_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_snd_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
v_a_590_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_579_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_579_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
else
{
lean_dec(v_a_572_);
lean_dec_ref(v_x_557_);
return v___x_574_;
}
}
else
{
lean_dec_ref(v_x_557_);
lean_dec_ref(v_x_556_);
return v___x_571_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_556_ = stack[0].m_obj;
lean_object* v_x_557_ = stack[1].m_obj;
lean_object* v_x_558_ = stack[2].m_obj;
lean_object* v___y_559_ = stack[3].m_obj;
lean_object* v___y_560_ = stack[4].m_obj;
lean_object* v___y_561_ = stack[5].m_obj;
lean_object* v___y_562_ = stack[6].m_obj;
lean_object* v___y_563_ = stack[7].m_obj;
lean_object* v_res_598_;
v_res_598_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(v_x_556_, v_x_557_, v_x_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
stack->m_obj
 = v_res_598_;
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = l_Lean_Expr_bvar___override(v___x_599_);
return v___x_600_;
}
}
lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0(lean_object* v_body_601_, lean_object* v_binderName_602_, uint8_t v_binderInfo_603_, lean_object* v_binderType_604_, lean_object* v_arg_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_ty_x27_613_; uint8_t v___x_625_; 
v___x_625_ = l_Lean_Expr_hasLooseBVars(v_body_601_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; 
v___x_626_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_binderType_604_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_a_627_);
lean_dec_ref_known(v___x_626_, 1);
v_ty_x27_613_ = v_a_627_;
goto v___jp_612_;
}
else
{
lean_dec(v_binderName_602_);
return v___x_626_;
}
}
else
{
lean_object* v___x_628_; 
lean_dec_ref(v_binderType_604_);
v___x_628_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0);
v_ty_x27_613_ = v___x_628_;
goto v___jp_612_;
}
v___jp_612_:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_expr_instantiate1(v_body_601_, v_arg_605_);
v___x_615_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_614_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_624_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_624_ == 0)
{
v___x_618_ = v___x_615_;
v_isShared_619_ = v_isSharedCheck_624_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_624_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_620_ = l_Lean_Expr_forallE___override(v_binderName_602_, v_ty_x27_613_, v_a_616_, v_binderInfo_603_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_620_);
v___x_622_ = v___x_618_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
else
{
lean_dec_ref(v_ty_x27_613_);
lean_dec(v_binderName_602_);
return v___x_615_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_601_ = stack[0].m_obj;
lean_object* v_binderName_602_ = stack[1].m_obj;
uint8_t v_binderInfo_603_ = stack[2].m_num;
lean_object* v_binderType_604_ = stack[3].m_obj;
lean_object* v_arg_605_ = stack[4].m_obj;
lean_object* v___y_606_ = stack[5].m_obj;
lean_object* v___y_607_ = stack[6].m_obj;
lean_object* v___y_608_ = stack[7].m_obj;
lean_object* v___y_609_ = stack[8].m_obj;
lean_object* v___y_610_ = stack[9].m_obj;
lean_object* v_res_629_;
v_res_629_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0(v_body_601_, v_binderName_602_, v_binderInfo_603_, v_binderType_604_, v_arg_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
stack->m_obj
 = v_res_629_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___boxed(lean_object* v_body_630_, lean_object* v_binderName_631_, lean_object* v_binderInfo_632_, lean_object* v_binderType_633_, lean_object* v_arg_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
uint8_t v_binderInfo_16092__boxed_641_; lean_object* v_res_642_; 
v_binderInfo_16092__boxed_641_ = lean_unbox(v_binderInfo_632_);
v_res_642_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0(v_body_630_, v_binderName_631_, v_binderInfo_16092__boxed_641_, v_binderType_633_, v_arg_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v_arg_634_);
lean_dec_ref(v_body_630_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1___boxed(lean_object* v_body_643_, lean_object* v_arg_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1(v_body_643_, v_arg_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v_arg_644_);
lean_dec_ref(v_body_643_);
return v_res_651_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__2));
v___x_656_ = l_Lean_Level_param___override(v___x_655_);
return v___x_656_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3);
v___x_658_ = l_Lean_Expr_sort___override(v___x_657_);
return v___x_658_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_box(0);
v___x_660_ = l_Lean_Level_succ___override(v___x_659_);
return v___x_660_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5);
v___x_662_ = l_Lean_Expr_sort___override(v___x_661_);
return v___x_662_;
}
}
lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(lean_object* v_e_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_a_671_; lean_object* v___y_677_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_st_ref_get(v_a_664_);
v___x_680_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v___x_679_, v_e_663_);
lean_dec(v___x_679_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v___x_681_; 
lean_inc_ref(v_e_663_);
v___x_681_ = l_Lean_Meta_isProof(v_e_663_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; uint8_t v___x_683_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v___x_681_, 1);
v___x_683_ = lean_unbox(v_a_682_);
lean_dec(v_a_682_);
if (v___x_683_ == 0)
{
switch(lean_obj_tag(v_e_663_))
{
case 5:
{
lean_object* v___x_684_; 
v___x_684_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg(v_e_663_, v_a_668_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v___x_684_, 1);
if (lean_obj_tag(v_a_685_) == 1)
{
lean_object* v_val_686_; lean_object* v___x_687_; 
v_val_686_ = lean_ctor_get(v_a_685_, 0);
lean_inc(v_val_686_);
lean_dec_ref_known(v_a_685_, 1);
v___x_687_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_val_686_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
v___y_677_ = v___x_687_;
goto v___jp_676_;
}
else
{
lean_object* v_dummy_688_; lean_object* v_nargs_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
lean_dec(v_a_685_);
v_dummy_688_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0);
v_nargs_689_ = l_Lean_Expr_getAppNumArgs(v_e_663_);
lean_inc(v_nargs_689_);
v___x_690_ = lean_mk_array(v_nargs_689_, v_dummy_688_);
v___x_691_ = lean_unsigned_to_nat(1u);
v___x_692_ = lean_nat_sub(v_nargs_689_, v___x_691_);
lean_dec(v_nargs_689_);
lean_inc_ref(v_e_663_);
v___x_693_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(v_e_663_, v___x_690_, v___x_692_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
v___y_677_ = v___x_693_;
goto v___jp_676_;
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_dec_ref_known(v_e_663_, 2);
v_a_694_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_684_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_684_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
case 7:
{
lean_object* v_binderName_702_; lean_object* v_binderType_703_; lean_object* v_body_704_; uint8_t v_binderInfo_705_; lean_object* v___x_706_; lean_object* v___f_707_; uint8_t v___x_708_; lean_object* v___x_709_; 
v_binderName_702_ = lean_ctor_get(v_e_663_, 0);
v_binderType_703_ = lean_ctor_get(v_e_663_, 1);
v_body_704_ = lean_ctor_get(v_e_663_, 2);
v_binderInfo_705_ = lean_ctor_get_uint8(v_e_663_, sizeof(void*)*3 + 8);
v___x_706_ = lean_box(v_binderInfo_705_);
lean_inc_ref_n(v_binderType_703_, 2);
lean_inc_n(v_binderName_702_, 2);
lean_inc_ref(v_body_704_);
v___f_707_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___boxed), 11, 4);
lean_closure_set(v___f_707_, 0, v_body_704_);
lean_closure_set(v___f_707_, 1, v_binderName_702_);
lean_closure_set(v___f_707_, 2, v___x_706_);
lean_closure_set(v___f_707_, 3, v_binderType_703_);
v___x_708_ = 0;
v___x_709_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(v_binderName_702_, v_binderInfo_705_, v_binderType_703_, v___f_707_, v___x_708_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
v___y_677_ = v___x_709_;
goto v___jp_676_;
}
case 6:
{
lean_object* v_binderName_710_; lean_object* v_binderType_711_; lean_object* v_body_712_; uint8_t v_binderInfo_713_; lean_object* v___x_714_; 
v_binderName_710_ = lean_ctor_get(v_e_663_, 0);
v_binderType_711_ = lean_ctor_get(v_e_663_, 1);
v_body_712_ = lean_ctor_get(v_e_663_, 2);
v_binderInfo_713_ = lean_ctor_get_uint8(v_e_663_, sizeof(void*)*3 + 8);
lean_inc_ref(v_e_663_);
v___x_714_ = l_Lean_Expr_etaExpandedStrict_x3f(v_e_663_);
if (lean_obj_tag(v___x_714_) == 1)
{
lean_object* v_val_715_; lean_object* v___x_716_; 
v_val_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_val_715_);
lean_dec_ref_known(v___x_714_, 1);
v___x_716_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_val_715_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
v___y_677_ = v___x_716_;
goto v___jp_676_;
}
else
{
lean_object* v___f_717_; uint8_t v___x_718_; lean_object* v___x_719_; 
lean_dec(v___x_714_);
lean_inc_ref(v_body_712_);
v___f_717_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1___boxed), 8, 1);
lean_closure_set(v___f_717_, 0, v_body_712_);
v___x_718_ = 0;
lean_inc_ref(v_binderType_711_);
lean_inc(v_binderName_710_);
v___x_719_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(v_binderName_710_, v_binderInfo_713_, v_binderType_711_, v___f_717_, v___x_718_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
v___y_677_ = v___x_719_;
goto v___jp_676_;
}
}
case 8:
{
lean_object* v_value_720_; lean_object* v_body_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_value_720_ = lean_ctor_get(v_e_663_, 2);
v_body_721_ = lean_ctor_get(v_e_663_, 3);
v___x_722_ = lean_expr_instantiate1(v_body_721_, v_value_720_);
v___x_723_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_722_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
v___y_677_ = v___x_723_;
goto v___jp_676_;
}
case 3:
{
uint8_t v___x_724_; 
v___x_724_ = l_Lean_Expr_isProp(v_e_663_);
if (v___x_724_ == 0)
{
uint8_t v___x_725_; 
v___x_725_ = l_Lean_Expr_isType(v_e_663_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
v___x_726_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4);
v_a_671_ = v___x_726_;
goto v___jp_670_;
}
else
{
lean_object* v___x_727_; 
v___x_727_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6);
v_a_671_ = v___x_727_;
goto v___jp_670_;
}
}
else
{
lean_object* v___x_728_; 
v___x_728_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0);
v_a_671_ = v___x_728_;
goto v___jp_670_;
}
}
case 4:
{
lean_object* v_declName_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_declName_729_ = lean_ctor_get(v_e_663_, 0);
v___x_730_ = lean_box(0);
lean_inc(v_declName_729_);
v___x_731_ = l_Lean_Expr_const___override(v_declName_729_, v___x_730_);
v_a_671_ = v___x_731_;
goto v___jp_670_;
}
case 10:
{
lean_object* v_expr_732_; lean_object* v___x_733_; 
v_expr_732_ = lean_ctor_get(v_e_663_, 1);
lean_inc_ref(v_expr_732_);
v___x_733_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_expr_732_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
v___y_677_ = v___x_733_;
goto v___jp_676_;
}
default: 
{
lean_object* v___x_734_; 
v___x_734_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0);
v_a_671_ = v___x_734_;
goto v___jp_670_;
}
}
}
else
{
lean_object* v___x_735_; 
v___x_735_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0);
v_a_671_ = v___x_735_;
goto v___jp_670_;
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec_ref(v_e_663_);
v_a_736_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_681_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_681_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
else
{
lean_object* v_val_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec_ref(v_e_663_);
v_val_744_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_680_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_val_744_);
lean_dec(v___x_680_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set_tag(v___x_746_, 0);
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_val_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
v___jp_670_:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_672_ = lean_st_ref_take(v_a_664_);
lean_inc_ref(v_a_671_);
v___x_673_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v___x_672_, v_e_663_, v_a_671_);
v___x_674_ = lean_st_ref_put(v_a_664_, v___x_673_);
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v_a_671_);
return v___x_675_;
}
v___jp_676_:
{
if (lean_obj_tag(v___y_677_) == 0)
{
lean_object* v_a_678_; 
v_a_678_ = lean_ctor_get(v___y_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v___y_677_, 1);
v_a_671_ = v_a_678_;
goto v___jp_670_;
}
else
{
lean_dec_ref(v_e_663_);
return v___y_677_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_663_ = stack[0].m_obj;
lean_object* v_a_664_ = stack[1].m_obj;
lean_object* v_a_665_ = stack[2].m_obj;
lean_object* v_a_666_ = stack[3].m_obj;
lean_object* v_a_667_ = stack[4].m_obj;
lean_object* v_a_668_ = stack[5].m_obj;
lean_object* v_res_752_;
v_res_752_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_e_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
stack->m_obj
 = v_res_752_;
}
lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1(lean_object* v_body_753_, lean_object* v_arg_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_expr_instantiate1(v_body_753_, v_arg_754_);
v___x_762_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_761_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
return v___x_762_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_753_ = stack[0].m_obj;
lean_object* v_arg_754_ = stack[1].m_obj;
lean_object* v___y_755_ = stack[2].m_obj;
lean_object* v___y_756_ = stack[3].m_obj;
lean_object* v___y_757_ = stack[4].m_obj;
lean_object* v___y_758_ = stack[5].m_obj;
lean_object* v___y_759_ = stack[6].m_obj;
lean_object* v_res_763_;
v_res_763_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1(v_body_753_, v_arg_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
stack->m_obj
 = v_res_763_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4___boxed(lean_object* v_x_764_, lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(v_x_764_, v_x_765_, v_x_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___boxed(lean_object* v_upperBound_774_, lean_object* v_args_775_, lean_object* v_a_776_, lean_object* v_b_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v_upperBound_774_, v_args_775_, v_a_776_, v_b_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v_args_775_);
lean_dec(v_upperBound_774_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___boxed(lean_object* v_snd_785_, lean_object* v_args_786_, lean_object* v_a_787_, lean_object* v_____r_788_, lean_object* v_fty_789_, lean_object* v_j_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_snd_785_, v_args_786_, v_a_787_, v_____r_788_, v_fty_789_, v_j_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
lean_dec(v_j_790_);
lean_dec(v_a_787_);
lean_dec_ref(v_args_786_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___boxed(lean_object* v_e_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_e_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
return v_res_805_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0(lean_object* v_00_u03b1_806_, lean_object* v_msg_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v_msg_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
return v___x_813_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_807_ = stack[1].m_obj;
lean_object* v___y_808_ = stack[2].m_obj;
lean_object* v___y_809_ = stack[3].m_obj;
lean_object* v___y_810_ = stack[4].m_obj;
lean_object* v___y_811_ = stack[5].m_obj;
lean_object* v_res_814_;
v_res_814_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0(lean_box(0), v_msg_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
stack->m_obj
 = v_res_814_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___boxed(lean_object* v_00_u03b1_815_, lean_object* v_msg_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0(v_00_u03b1_815_, v_msg_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
return v_res_822_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1(lean_object* v_upperBound_823_, lean_object* v_args_824_, lean_object* v_inst_825_, lean_object* v_R_826_, lean_object* v_a_827_, lean_object* v_b_828_, lean_object* v_c_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v_upperBound_823_, v_args_824_, v_a_827_, v_b_828_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
return v___x_836_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_823_ = stack[0].m_obj;
lean_object* v_args_824_ = stack[1].m_obj;
lean_object* v_a_827_ = stack[4].m_obj;
lean_object* v_b_828_ = stack[5].m_obj;
lean_object* v___y_830_ = stack[7].m_obj;
lean_object* v___y_831_ = stack[8].m_obj;
lean_object* v___y_832_ = stack[9].m_obj;
lean_object* v___y_833_ = stack[10].m_obj;
lean_object* v___y_834_ = stack[11].m_obj;
lean_object* v_res_837_;
v_res_837_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1(v_upperBound_823_, v_args_824_, lean_box(0), lean_box(0), v_a_827_, v_b_828_, lean_box(0), v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
stack->m_obj
 = v_res_837_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___boxed(lean_object* v_upperBound_838_, lean_object* v_args_839_, lean_object* v_inst_840_, lean_object* v_R_841_, lean_object* v_a_842_, lean_object* v_b_843_, lean_object* v_c_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1(v_upperBound_838_, v_args_839_, v_inst_840_, v_R_841_, v_a_842_, v_b_843_, v_c_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v_args_839_);
lean_dec(v_upperBound_838_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2(lean_object* v_00_u03b2_852_, lean_object* v_m_853_, lean_object* v_a_854_, lean_object* v_b_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v_m_853_, v_a_854_, v_b_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3(lean_object* v_00_u03b2_857_, lean_object* v_m_858_, lean_object* v_a_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v_m_858_, v_a_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___boxed(lean_object* v_00_u03b2_861_, lean_object* v_m_862_, lean_object* v_a_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3(v_00_u03b2_861_, v_m_862_, v_a_863_);
lean_dec_ref(v_a_863_);
lean_dec_ref(v_m_862_);
return v_res_864_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3(lean_object* v_00_u03b2_865_, lean_object* v_a_866_, lean_object* v_x_867_){
_start:
{
uint8_t v___x_868_; 
v___x_868_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_866_, v_x_867_);
return v___x_868_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_866_ = stack[1].m_obj;
lean_object* v_x_867_ = stack[2].m_obj;
uint8_t v_res_869_;
v_res_869_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3(lean_box(0), v_a_866_, v_x_867_);
stack->m_num = v_res_869_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___boxed(lean_object* v_00_u03b2_870_, lean_object* v_a_871_, lean_object* v_x_872_){
_start:
{
uint8_t v_res_873_; lean_object* v_r_874_; 
v_res_873_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3(v_00_u03b2_870_, v_a_871_, v_x_872_);
lean_dec(v_x_872_);
lean_dec_ref(v_a_871_);
v_r_874_ = lean_box(v_res_873_);
return v_r_874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4(lean_object* v_00_u03b2_875_, lean_object* v_data_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(v_data_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5(lean_object* v_00_u03b2_878_, lean_object* v_a_879_, lean_object* v_b_880_, lean_object* v_x_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(v_a_879_, v_b_880_, v_x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7(lean_object* v_00_u03b2_883_, lean_object* v_a_884_, lean_object* v_x_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(v_a_884_, v_x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___boxed(lean_object* v_00_u03b2_887_, lean_object* v_a_888_, lean_object* v_x_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7(v_00_u03b2_887_, v_a_888_, v_x_889_);
lean_dec(v_x_889_);
lean_dec_ref(v_a_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_891_, lean_object* v_i_892_, lean_object* v_source_893_, lean_object* v_target_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6___redArg(v_i_892_, v_source_893_, v_target_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_896_, lean_object* v_x_897_, lean_object* v_x_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9___redArg(v_x_897_, v_x_898_);
return v___x_899_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_900_ = lean_box(0);
v___x_901_ = lean_unsigned_to_nat(16u);
v___x_902_ = lean_mk_array(v___x_901_, v___x_900_);
return v___x_902_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0);
v___x_904_ = lean_unsigned_to_nat(0u);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v___x_903_);
return v___x_905_;
}
}
lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(lean_object* v_e_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_912_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1);
v___x_913_ = lean_st_mk_ref(v___x_912_);
v___x_914_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_e_906_, v___x_913_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_923_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_923_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_919_ = lean_st_ref_get(v___x_913_);
lean_dec(v___x_913_);
lean_dec(v___x_919_);
if (v_isShared_918_ == 0)
{
v___x_921_ = v___x_917_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_915_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
else
{
lean_dec(v___x_913_);
return v___x_914_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_906_ = stack[0].m_obj;
lean_object* v_a_907_ = stack[1].m_obj;
lean_object* v_a_908_ = stack[2].m_obj;
lean_object* v_a_909_ = stack[3].m_obj;
lean_object* v_a_910_ = stack[4].m_obj;
lean_object* v_res_924_;
v_res_924_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(v_e_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
stack->m_obj
 = v_res_924_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___boxed(lean_object* v_e_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(v_e_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
return v_res_931_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(lean_object* v_m_932_, lean_object* v_a_933_){
_start:
{
lean_object* v_buckets_934_; lean_object* v___x_935_; uint64_t v___x_936_; uint64_t v___x_937_; uint64_t v___x_938_; uint64_t v_fold_939_; uint64_t v___x_940_; uint64_t v___x_941_; uint64_t v___x_942_; size_t v___x_943_; size_t v___x_944_; size_t v___x_945_; size_t v___x_946_; size_t v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v_buckets_934_ = lean_ctor_get(v_m_932_, 1);
v___x_935_ = lean_array_get_size(v_buckets_934_);
v___x_936_ = l_Lean_Expr_hash(v_a_933_);
v___x_937_ = 32ULL;
v___x_938_ = lean_uint64_shift_right(v___x_936_, v___x_937_);
v_fold_939_ = lean_uint64_xor(v___x_936_, v___x_938_);
v___x_940_ = 16ULL;
v___x_941_ = lean_uint64_shift_right(v_fold_939_, v___x_940_);
v___x_942_ = lean_uint64_xor(v_fold_939_, v___x_941_);
v___x_943_ = lean_uint64_to_usize(v___x_942_);
v___x_944_ = lean_usize_of_nat(v___x_935_);
v___x_945_ = ((size_t)1ULL);
v___x_946_ = lean_usize_sub(v___x_944_, v___x_945_);
v___x_947_ = lean_usize_land(v___x_943_, v___x_946_);
v___x_948_ = lean_array_uget_borrowed(v_buckets_934_, v___x_947_);
v___x_949_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_933_, v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_932_ = stack[0].m_obj;
lean_object* v_a_933_ = stack[1].m_obj;
uint8_t v_res_950_;
v_res_950_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_m_932_, v_a_933_);
stack->m_num = v_res_950_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg___boxed(lean_object* v_m_951_, lean_object* v_a_952_){
_start:
{
uint8_t v_res_953_; lean_object* v_r_954_; 
v_res_953_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_m_951_, v_a_952_);
lean_dec_ref(v_a_952_);
lean_dec_ref(v_m_951_);
v_r_954_ = lean_box(v_res_953_);
return v_r_954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(lean_object* v_m_955_, lean_object* v_a_956_, lean_object* v_b_957_){
_start:
{
lean_object* v_size_958_; lean_object* v_buckets_959_; lean_object* v___x_960_; uint64_t v___x_961_; uint64_t v___x_962_; uint64_t v___x_963_; uint64_t v_fold_964_; uint64_t v___x_965_; uint64_t v___x_966_; uint64_t v___x_967_; size_t v___x_968_; size_t v___x_969_; size_t v___x_970_; size_t v___x_971_; size_t v___x_972_; lean_object* v_bkt_973_; uint8_t v___x_974_; 
v_size_958_ = lean_ctor_get(v_m_955_, 0);
v_buckets_959_ = lean_ctor_get(v_m_955_, 1);
v___x_960_ = lean_array_get_size(v_buckets_959_);
v___x_961_ = l_Lean_Expr_hash(v_a_956_);
v___x_962_ = 32ULL;
v___x_963_ = lean_uint64_shift_right(v___x_961_, v___x_962_);
v_fold_964_ = lean_uint64_xor(v___x_961_, v___x_963_);
v___x_965_ = 16ULL;
v___x_966_ = lean_uint64_shift_right(v_fold_964_, v___x_965_);
v___x_967_ = lean_uint64_xor(v_fold_964_, v___x_966_);
v___x_968_ = lean_uint64_to_usize(v___x_967_);
v___x_969_ = lean_usize_of_nat(v___x_960_);
v___x_970_ = ((size_t)1ULL);
v___x_971_ = lean_usize_sub(v___x_969_, v___x_970_);
v___x_972_ = lean_usize_land(v___x_968_, v___x_971_);
v_bkt_973_ = lean_array_uget_borrowed(v_buckets_959_, v___x_972_);
v___x_974_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_956_, v_bkt_973_);
if (v___x_974_ == 0)
{
lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_995_; 
lean_inc_ref(v_buckets_959_);
lean_inc(v_size_958_);
v_isSharedCheck_995_ = !lean_is_exclusive(v_m_955_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; lean_object* v_unused_997_; 
v_unused_996_ = lean_ctor_get(v_m_955_, 1);
lean_dec(v_unused_996_);
v_unused_997_ = lean_ctor_get(v_m_955_, 0);
lean_dec(v_unused_997_);
v___x_976_ = v_m_955_;
v_isShared_977_ = v_isSharedCheck_995_;
goto v_resetjp_975_;
}
else
{
lean_dec(v_m_955_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_995_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v_size_x27_979_; lean_object* v___x_980_; lean_object* v_buckets_x27_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_978_ = lean_unsigned_to_nat(1u);
v_size_x27_979_ = lean_nat_add(v_size_958_, v___x_978_);
lean_dec(v_size_958_);
lean_inc(v_bkt_973_);
v___x_980_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_980_, 0, v_a_956_);
lean_ctor_set(v___x_980_, 1, v_b_957_);
lean_ctor_set(v___x_980_, 2, v_bkt_973_);
v_buckets_x27_981_ = lean_array_uset(v_buckets_959_, v___x_972_, v___x_980_);
v___x_982_ = lean_unsigned_to_nat(4u);
v___x_983_ = lean_nat_mul(v_size_x27_979_, v___x_982_);
v___x_984_ = lean_unsigned_to_nat(3u);
v___x_985_ = lean_nat_div(v___x_983_, v___x_984_);
lean_dec(v___x_983_);
v___x_986_ = lean_array_get_size(v_buckets_x27_981_);
v___x_987_ = lean_nat_dec_le(v___x_985_, v___x_986_);
lean_dec(v___x_985_);
if (v___x_987_ == 0)
{
lean_object* v_val_988_; lean_object* v___x_990_; 
v_val_988_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(v_buckets_x27_981_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 1, v_val_988_);
lean_ctor_set(v___x_976_, 0, v_size_x27_979_);
v___x_990_ = v___x_976_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_size_x27_979_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_val_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
else
{
lean_object* v___x_993_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 1, v_buckets_x27_981_);
lean_ctor_set(v___x_976_, 0, v_size_x27_979_);
v___x_993_ = v___x_976_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_size_x27_979_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_buckets_x27_981_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
else
{
lean_dec(v_b_957_);
lean_dec_ref(v_a_956_);
return v_m_955_;
}
}
}
lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(lean_object* v_e_1003_, uint8_t v_omitTopForall_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
switch(lean_obj_tag(v_e_1003_))
{
case 4:
{
lean_object* v_declName_1011_; lean_object* v___x_1012_; lean_object* v_seen_1013_; lean_object* v_consts_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1041_; 
v_declName_1011_ = lean_ctor_get(v_e_1003_, 0);
lean_inc(v_declName_1011_);
lean_dec_ref_known(v_e_1003_, 2);
v___x_1012_ = lean_st_ref_take(v_a_1005_);
v_seen_1013_ = lean_ctor_get(v___x_1012_, 0);
v_consts_1014_ = lean_ctor_get(v___x_1012_, 1);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1016_ = v___x_1012_;
v_isShared_1017_ = v_isSharedCheck_1041_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_consts_1014_);
lean_inc(v_seen_1013_);
lean_dec(v___x_1012_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1041_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
lean_inc(v_declName_1011_);
v___x_1018_ = l_Lean_NameSet_insert(v_consts_1014_, v_declName_1011_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 1, v___x_1018_);
v___x_1020_ = v___x_1016_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_seen_1013_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_st_ref_put(v_a_1005_, v___x_1020_);
v___x_1022_ = l_Lean_Name_eraseMacroScopes(v_declName_1011_);
lean_dec(v_declName_1011_);
if (lean_obj_tag(v___x_1022_) == 1)
{
lean_object* v_str_1023_; lean_object* v___x_1024_; uint32_t v___x_1025_; uint32_t v___x_1026_; uint8_t v___x_1027_; 
v_str_1023_ = lean_ctor_get(v___x_1022_, 1);
lean_inc_ref(v_str_1023_);
lean_dec_ref_known(v___x_1022_, 2);
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = lean_string_utf8_get(v_str_1023_, v___x_1024_);
v___x_1026_ = 97;
v___x_1027_ = lean_uint32_dec_le(v___x_1026_, v___x_1025_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = lean_string_utf8_set(v_str_1023_, v___x_1024_, v___x_1025_);
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
return v___x_1029_;
}
else
{
uint32_t v___x_1030_; uint8_t v___x_1031_; 
v___x_1030_ = 122;
v___x_1031_ = lean_uint32_dec_le(v___x_1025_, v___x_1030_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_string_utf8_set(v_str_1023_, v___x_1024_, v___x_1025_);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
else
{
uint32_t v___x_1034_; uint32_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1034_ = 4294967264;
v___x_1035_ = lean_uint32_add(v___x_1025_, v___x_1034_);
v___x_1036_ = lean_string_utf8_set(v_str_1023_, v___x_1024_, v___x_1035_);
v___x_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
return v___x_1037_;
}
}
}
else
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
lean_dec(v___x_1022_);
v___x_1038_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
return v___x_1039_;
}
}
}
}
case 5:
{
lean_object* v_fn_1042_; lean_object* v_arg_1043_; uint8_t v___x_1044_; lean_object* v___x_1045_; lean_object* v_a_1046_; lean_object* v___x_1047_; lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1056_; 
v_fn_1042_ = lean_ctor_get(v_e_1003_, 0);
lean_inc_ref(v_fn_1042_);
v_arg_1043_ = lean_ctor_get(v_e_1003_, 1);
lean_inc_ref(v_arg_1043_);
lean_dec_ref_known(v_e_1003_, 2);
v___x_1044_ = 0;
v___x_1045_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_fn_1042_, v___x_1044_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref(v___x_1045_);
v___x_1047_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_arg_1043_, v___x_1044_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1050_ = v___x_1047_;
v_isShared_1051_ = v_isSharedCheck_1056_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1047_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1056_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1052_ = lean_string_append(v_a_1046_, v_a_1048_);
lean_dec(v_a_1048_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v___x_1052_);
v___x_1054_ = v___x_1050_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
case 7:
{
lean_object* v_binderType_1057_; lean_object* v_body_1058_; uint8_t v___x_1059_; lean_object* v___x_1060_; lean_object* v_a_1061_; 
v_binderType_1057_ = lean_ctor_get(v_e_1003_, 1);
lean_inc_ref(v_binderType_1057_);
v_body_1058_ = lean_ctor_get(v_e_1003_, 2);
lean_inc_ref(v_body_1058_);
lean_dec_ref_known(v_e_1003_, 3);
v___x_1059_ = 0;
v___x_1060_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_binderType_1057_, v___x_1059_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
lean_dec_ref(v___x_1060_);
if (v_omitTopForall_1004_ == 0)
{
goto v___jp_1062_;
}
else
{
lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1075_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1076_ = lean_string_dec_eq(v_a_1061_, v___x_1075_);
if (v___x_1076_ == 0)
{
goto v___jp_1062_;
}
else
{
lean_object* v___x_1077_; 
lean_dec(v_a_1061_);
v___x_1077_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_body_1058_, v_omitTopForall_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
return v___x_1077_;
}
}
v___jp_1062_:
{
lean_object* v___x_1063_; lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1074_; 
v___x_1063_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_body_1058_, v___x_1059_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1074_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1074_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1068_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0));
v___x_1069_ = lean_string_append(v___x_1068_, v_a_1061_);
lean_dec(v_a_1061_);
v___x_1070_ = lean_string_append(v___x_1069_, v_a_1064_);
lean_dec(v_a_1064_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1070_);
v___x_1072_ = v___x_1066_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
case 3:
{
lean_object* v_u_1078_; 
v_u_1078_ = lean_ctor_get(v_e_1003_, 0);
lean_inc(v_u_1078_);
lean_dec_ref_known(v_e_1003_, 1);
switch(lean_obj_tag(v_u_1078_))
{
case 0:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__1));
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
return v___x_1080_;
}
case 1:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_dec_ref_known(v_u_1078_, 1);
v___x_1081_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__2));
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
return v___x_1082_;
}
default: 
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec(v_u_1078_);
v___x_1083_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__3));
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
}
}
default: 
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
lean_dec_ref(v_e_1003_);
v___x_1085_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
return v___x_1086_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1003_ = stack[0].m_obj;
uint8_t v_omitTopForall_1004_ = stack[1].m_num;
lean_object* v_a_1005_ = stack[2].m_obj;
lean_object* v_a_1006_ = stack[3].m_obj;
lean_object* v_a_1007_ = stack[4].m_obj;
lean_object* v_a_1008_ = stack[5].m_obj;
lean_object* v_a_1009_ = stack[6].m_obj;
lean_object* v_res_1087_;
v_res_1087_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(v_e_1003_, v_omitTopForall_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
stack->m_obj
 = v_res_1087_;
}
lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(lean_object* v_e_1088_, uint8_t v_omitTopForall_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v___x_1096_; lean_object* v_seen_1097_; uint8_t v___x_1098_; 
v___x_1096_ = lean_st_ref_get(v_a_1090_);
v_seen_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc_ref(v_seen_1097_);
lean_dec(v___x_1096_);
v___x_1098_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_seen_1097_, v_e_1088_);
lean_dec_ref(v_seen_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1120_; 
lean_inc_ref(v_e_1088_);
v___x_1099_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(v_e_1088_, v_omitTopForall_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1102_ = v___x_1099_;
v_isShared_1103_ = v_isSharedCheck_1120_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1120_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v_seen_1105_; lean_object* v_consts_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1119_; 
v___x_1104_ = lean_st_ref_take(v_a_1090_);
v_seen_1105_ = lean_ctor_get(v___x_1104_, 0);
v_consts_1106_ = lean_ctor_get(v___x_1104_, 1);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1108_ = v___x_1104_;
v_isShared_1109_ = v_isSharedCheck_1119_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_consts_1106_);
lean_inc(v_seen_1105_);
lean_dec(v___x_1104_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1119_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___x_1110_ = lean_box(0);
v___x_1111_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(v_seen_1105_, v_e_1088_, v___x_1110_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1111_);
v___x_1113_ = v___x_1108_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1111_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_consts_1106_);
v___x_1113_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1114_; lean_object* v___x_1116_; 
v___x_1114_ = lean_st_ref_put(v_a_1090_, v___x_1113_);
if (v_isShared_1103_ == 0)
{
v___x_1116_ = v___x_1102_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1100_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
else
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_dec_ref(v_e_1088_);
v___x_1121_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
return v___x_1122_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1088_ = stack[0].m_obj;
uint8_t v_omitTopForall_1089_ = stack[1].m_num;
lean_object* v_a_1090_ = stack[2].m_obj;
lean_object* v_a_1091_ = stack[3].m_obj;
lean_object* v_a_1092_ = stack[4].m_obj;
lean_object* v_a_1093_ = stack[5].m_obj;
lean_object* v_a_1094_ = stack[6].m_obj;
lean_object* v_res_1123_;
v_res_1123_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_e_1088_, v_omitTopForall_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
stack->m_obj
 = v_res_1123_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___boxed(lean_object* v_e_1124_, lean_object* v_omitTopForall_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
uint8_t v_omitTopForall_boxed_1132_; lean_object* v_res_1133_; 
v_omitTopForall_boxed_1132_ = lean_unbox(v_omitTopForall_1125_);
v_res_1133_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_e_1124_, v_omitTopForall_boxed_1132_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec(v_a_1126_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___boxed(lean_object* v_e_1134_, lean_object* v_omitTopForall_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
uint8_t v_omitTopForall_boxed_1142_; lean_object* v_res_1143_; 
v_omitTopForall_boxed_1142_ = lean_unbox(v_omitTopForall_1135_);
v_res_1143_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(v_e_1134_, v_omitTopForall_boxed_1142_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
return v_res_1143_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0(lean_object* v_00_u03b2_1144_, lean_object* v_m_1145_, lean_object* v_a_1146_){
_start:
{
uint8_t v___x_1147_; 
v___x_1147_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_m_1145_, v_a_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1145_ = stack[1].m_obj;
lean_object* v_a_1146_ = stack[2].m_obj;
uint8_t v_res_1148_;
v_res_1148_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0(lean_box(0), v_m_1145_, v_a_1146_);
stack->m_num = v_res_1148_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___boxed(lean_object* v_00_u03b2_1149_, lean_object* v_m_1150_, lean_object* v_a_1151_){
_start:
{
uint8_t v_res_1152_; lean_object* v_r_1153_; 
v_res_1152_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0(v_00_u03b2_1149_, v_m_1150_, v_a_1151_);
lean_dec_ref(v_a_1151_);
lean_dec_ref(v_m_1150_);
v_r_1153_ = lean_box(v_res_1152_);
return v_r_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1(lean_object* v_00_u03b2_1154_, lean_object* v_m_1155_, lean_object* v_a_1156_, lean_object* v_b_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(v_m_1155_, v_a_1156_, v_b_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__3_splitter___redArg(lean_object* v_e_1159_, lean_object* v_h__1_1160_, lean_object* v_h__2_1161_, lean_object* v_h__3_1162_, lean_object* v_h__4_1163_, lean_object* v_h__5_1164_, lean_object* v_h__6_1165_, lean_object* v_h__7_1166_){
_start:
{
switch(lean_obj_tag(v_e_1159_))
{
case 4:
{
lean_object* v_declName_1167_; lean_object* v_us_1168_; lean_object* v___x_1169_; 
lean_dec(v_h__7_1166_);
lean_dec(v_h__6_1165_);
lean_dec(v_h__5_1164_);
lean_dec(v_h__4_1163_);
lean_dec(v_h__3_1162_);
lean_dec(v_h__2_1161_);
v_declName_1167_ = lean_ctor_get(v_e_1159_, 0);
lean_inc(v_declName_1167_);
v_us_1168_ = lean_ctor_get(v_e_1159_, 1);
lean_inc(v_us_1168_);
lean_dec_ref_known(v_e_1159_, 2);
v___x_1169_ = lean_apply_2(v_h__1_1160_, v_declName_1167_, v_us_1168_);
return v___x_1169_;
}
case 5:
{
lean_object* v_fn_1170_; lean_object* v_arg_1171_; lean_object* v___x_1172_; 
lean_dec(v_h__7_1166_);
lean_dec(v_h__6_1165_);
lean_dec(v_h__5_1164_);
lean_dec(v_h__4_1163_);
lean_dec(v_h__3_1162_);
lean_dec(v_h__1_1160_);
v_fn_1170_ = lean_ctor_get(v_e_1159_, 0);
lean_inc_ref(v_fn_1170_);
v_arg_1171_ = lean_ctor_get(v_e_1159_, 1);
lean_inc_ref(v_arg_1171_);
lean_dec_ref_known(v_e_1159_, 2);
v___x_1172_ = lean_apply_2(v_h__2_1161_, v_fn_1170_, v_arg_1171_);
return v___x_1172_;
}
case 7:
{
lean_object* v_binderName_1173_; lean_object* v_binderType_1174_; lean_object* v_body_1175_; uint8_t v_binderInfo_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec(v_h__7_1166_);
lean_dec(v_h__6_1165_);
lean_dec(v_h__5_1164_);
lean_dec(v_h__4_1163_);
lean_dec(v_h__2_1161_);
lean_dec(v_h__1_1160_);
v_binderName_1173_ = lean_ctor_get(v_e_1159_, 0);
lean_inc(v_binderName_1173_);
v_binderType_1174_ = lean_ctor_get(v_e_1159_, 1);
lean_inc_ref(v_binderType_1174_);
v_body_1175_ = lean_ctor_get(v_e_1159_, 2);
lean_inc_ref(v_body_1175_);
v_binderInfo_1176_ = lean_ctor_get_uint8(v_e_1159_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1159_, 3);
v___x_1177_ = lean_box(v_binderInfo_1176_);
v___x_1178_ = lean_apply_4(v_h__3_1162_, v_binderName_1173_, v_binderType_1174_, v_body_1175_, v___x_1177_);
return v___x_1178_;
}
case 3:
{
lean_object* v_u_1179_; 
lean_dec(v_h__7_1166_);
lean_dec(v_h__3_1162_);
lean_dec(v_h__2_1161_);
lean_dec(v_h__1_1160_);
v_u_1179_ = lean_ctor_get(v_e_1159_, 0);
lean_inc(v_u_1179_);
lean_dec_ref_known(v_e_1159_, 1);
switch(lean_obj_tag(v_u_1179_))
{
case 0:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
lean_dec(v_h__6_1165_);
lean_dec(v_h__5_1164_);
v___x_1180_ = lean_box(0);
v___x_1181_ = lean_apply_1(v_h__4_1163_, v___x_1180_);
return v___x_1181_;
}
case 1:
{
lean_object* v_a_1182_; lean_object* v___x_1183_; 
lean_dec(v_h__6_1165_);
lean_dec(v_h__4_1163_);
v_a_1182_ = lean_ctor_get(v_u_1179_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v_u_1179_, 1);
v___x_1183_ = lean_apply_1(v_h__5_1164_, v_a_1182_);
return v___x_1183_;
}
default: 
{
lean_object* v___x_1184_; 
lean_dec(v_h__5_1164_);
lean_dec(v_h__4_1163_);
v___x_1184_ = lean_apply_3(v_h__6_1165_, v_u_1179_, lean_box(0), lean_box(0));
return v___x_1184_;
}
}
}
default: 
{
lean_object* v___x_1185_; 
lean_dec(v_h__6_1165_);
lean_dec(v_h__5_1164_);
lean_dec(v_h__4_1163_);
lean_dec(v_h__3_1162_);
lean_dec(v_h__2_1161_);
lean_dec(v_h__1_1160_);
v___x_1185_ = lean_apply_7(v_h__7_1166_, v_e_1159_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1185_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__3_splitter(lean_object* v_motive_1186_, lean_object* v_e_1187_, lean_object* v_h__1_1188_, lean_object* v_h__2_1189_, lean_object* v_h__3_1190_, lean_object* v_h__4_1191_, lean_object* v_h__5_1192_, lean_object* v_h__6_1193_, lean_object* v_h__7_1194_){
_start:
{
switch(lean_obj_tag(v_e_1187_))
{
case 4:
{
lean_object* v_declName_1195_; lean_object* v_us_1196_; lean_object* v___x_1197_; 
lean_dec(v_h__7_1194_);
lean_dec(v_h__6_1193_);
lean_dec(v_h__5_1192_);
lean_dec(v_h__4_1191_);
lean_dec(v_h__3_1190_);
lean_dec(v_h__2_1189_);
v_declName_1195_ = lean_ctor_get(v_e_1187_, 0);
lean_inc(v_declName_1195_);
v_us_1196_ = lean_ctor_get(v_e_1187_, 1);
lean_inc(v_us_1196_);
lean_dec_ref_known(v_e_1187_, 2);
v___x_1197_ = lean_apply_2(v_h__1_1188_, v_declName_1195_, v_us_1196_);
return v___x_1197_;
}
case 5:
{
lean_object* v_fn_1198_; lean_object* v_arg_1199_; lean_object* v___x_1200_; 
lean_dec(v_h__7_1194_);
lean_dec(v_h__6_1193_);
lean_dec(v_h__5_1192_);
lean_dec(v_h__4_1191_);
lean_dec(v_h__3_1190_);
lean_dec(v_h__1_1188_);
v_fn_1198_ = lean_ctor_get(v_e_1187_, 0);
lean_inc_ref(v_fn_1198_);
v_arg_1199_ = lean_ctor_get(v_e_1187_, 1);
lean_inc_ref(v_arg_1199_);
lean_dec_ref_known(v_e_1187_, 2);
v___x_1200_ = lean_apply_2(v_h__2_1189_, v_fn_1198_, v_arg_1199_);
return v___x_1200_;
}
case 7:
{
lean_object* v_binderName_1201_; lean_object* v_binderType_1202_; lean_object* v_body_1203_; uint8_t v_binderInfo_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_dec(v_h__7_1194_);
lean_dec(v_h__6_1193_);
lean_dec(v_h__5_1192_);
lean_dec(v_h__4_1191_);
lean_dec(v_h__2_1189_);
lean_dec(v_h__1_1188_);
v_binderName_1201_ = lean_ctor_get(v_e_1187_, 0);
lean_inc(v_binderName_1201_);
v_binderType_1202_ = lean_ctor_get(v_e_1187_, 1);
lean_inc_ref(v_binderType_1202_);
v_body_1203_ = lean_ctor_get(v_e_1187_, 2);
lean_inc_ref(v_body_1203_);
v_binderInfo_1204_ = lean_ctor_get_uint8(v_e_1187_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1187_, 3);
v___x_1205_ = lean_box(v_binderInfo_1204_);
v___x_1206_ = lean_apply_4(v_h__3_1190_, v_binderName_1201_, v_binderType_1202_, v_body_1203_, v___x_1205_);
return v___x_1206_;
}
case 3:
{
lean_object* v_u_1207_; 
lean_dec(v_h__7_1194_);
lean_dec(v_h__3_1190_);
lean_dec(v_h__2_1189_);
lean_dec(v_h__1_1188_);
v_u_1207_ = lean_ctor_get(v_e_1187_, 0);
lean_inc(v_u_1207_);
lean_dec_ref_known(v_e_1187_, 1);
switch(lean_obj_tag(v_u_1207_))
{
case 0:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec(v_h__6_1193_);
lean_dec(v_h__5_1192_);
v___x_1208_ = lean_box(0);
v___x_1209_ = lean_apply_1(v_h__4_1191_, v___x_1208_);
return v___x_1209_;
}
case 1:
{
lean_object* v_a_1210_; lean_object* v___x_1211_; 
lean_dec(v_h__6_1193_);
lean_dec(v_h__4_1191_);
v_a_1210_ = lean_ctor_get(v_u_1207_, 0);
lean_inc(v_a_1210_);
lean_dec_ref_known(v_u_1207_, 1);
v___x_1211_ = lean_apply_1(v_h__5_1192_, v_a_1210_);
return v___x_1211_;
}
default: 
{
lean_object* v___x_1212_; 
lean_dec(v_h__5_1192_);
lean_dec(v_h__4_1191_);
v___x_1212_ = lean_apply_3(v_h__6_1193_, v_u_1207_, lean_box(0), lean_box(0));
return v___x_1212_;
}
}
}
default: 
{
lean_object* v___x_1213_; 
lean_dec(v_h__6_1193_);
lean_dec(v_h__5_1192_);
lean_dec(v_h__4_1191_);
lean_dec(v_h__3_1190_);
lean_dec(v_h__2_1189_);
lean_dec(v_h__1_1188_);
v___x_1213_ = lean_apply_7(v_h__7_1194_, v_e_1187_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1213_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__1_splitter___redArg(lean_object* v_x_1214_, lean_object* v_h__1_1215_, lean_object* v_h__2_1216_){
_start:
{
if (lean_obj_tag(v_x_1214_) == 1)
{
lean_object* v_pre_1217_; lean_object* v_str_1218_; lean_object* v___x_1219_; 
lean_dec(v_h__2_1216_);
v_pre_1217_ = lean_ctor_get(v_x_1214_, 0);
lean_inc(v_pre_1217_);
v_str_1218_ = lean_ctor_get(v_x_1214_, 1);
lean_inc_ref(v_str_1218_);
lean_dec_ref_known(v_x_1214_, 2);
v___x_1219_ = lean_apply_2(v_h__1_1215_, v_pre_1217_, v_str_1218_);
return v___x_1219_;
}
else
{
lean_object* v___x_1220_; 
lean_dec(v_h__1_1215_);
v___x_1220_ = lean_apply_2(v_h__2_1216_, v_x_1214_, lean_box(0));
return v___x_1220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__1_splitter(lean_object* v_motive_1221_, lean_object* v_x_1222_, lean_object* v_h__1_1223_, lean_object* v_h__2_1224_){
_start:
{
if (lean_obj_tag(v_x_1222_) == 1)
{
lean_object* v_pre_1225_; lean_object* v_str_1226_; lean_object* v___x_1227_; 
lean_dec(v_h__2_1224_);
v_pre_1225_ = lean_ctor_get(v_x_1222_, 0);
lean_inc(v_pre_1225_);
v_str_1226_ = lean_ctor_get(v_x_1222_, 1);
lean_inc_ref(v_str_1226_);
lean_dec_ref_known(v_x_1222_, 2);
v___x_1227_ = lean_apply_2(v_h__1_1223_, v_pre_1225_, v_str_1226_);
return v___x_1227_;
}
else
{
lean_object* v___x_1228_; 
lean_dec(v_h__1_1223_);
v___x_1228_ = lean_apply_2(v_h__2_1224_, v_x_1222_, lean_box(0));
return v___x_1228_;
}
}
}
lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore(lean_object* v_e_1229_, uint8_t v_omitTopForall_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_e_1229_, v_omitTopForall_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
return v___x_1237_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1229_ = stack[0].m_obj;
uint8_t v_omitTopForall_1230_ = stack[1].m_num;
lean_object* v_a_1231_ = stack[2].m_obj;
lean_object* v_a_1232_ = stack[3].m_obj;
lean_object* v_a_1233_ = stack[4].m_obj;
lean_object* v_a_1234_ = stack[5].m_obj;
lean_object* v_a_1235_ = stack[6].m_obj;
lean_object* v_res_1238_;
v_res_1238_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore(v_e_1229_, v_omitTopForall_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
stack->m_obj
 = v_res_1238_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore___boxed(lean_object* v_e_1239_, lean_object* v_omitTopForall_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
uint8_t v_omitTopForall_boxed_1247_; lean_object* v_res_1248_; 
v_omitTopForall_boxed_1247_ = lean_unbox(v_omitTopForall_1240_);
v_res_1248_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore(v_e_1239_, v_omitTopForall_boxed_1247_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
return v_res_1248_;
}
}
lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(lean_object* v_e_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
if (lean_obj_tag(v_e_1250_) == 7)
{
lean_object* v_binderType_1257_; lean_object* v_body_1258_; lean_object* v___x_1259_; 
v_binderType_1257_ = lean_ctor_get(v_e_1250_, 1);
lean_inc_ref(v_binderType_1257_);
v_body_1258_ = lean_ctor_get(v_e_1250_, 2);
lean_inc_ref(v_body_1258_);
lean_dec_ref_known(v_e_1250_, 3);
v___x_1259_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(v_body_1258_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v_fst_1261_; lean_object* v_snd_1262_; uint8_t v___x_1263_; lean_object* v___x_1264_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___x_1259_, 1);
v_fst_1261_ = lean_ctor_get(v_a_1260_, 0);
v_snd_1262_ = lean_ctor_get(v_a_1260_, 1);
v___x_1263_ = 1;
v___x_1264_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_binderType_1257_, v___x_1263_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1289_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1267_ = v___x_1264_;
v_isShared_1268_ = v_isSharedCheck_1289_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1264_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1289_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1269_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1270_ = lean_string_dec_eq(v_a_1265_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1283_; 
lean_inc(v_snd_1262_);
lean_inc(v_fst_1261_);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_a_1260_);
if (v_isSharedCheck_1283_ == 0)
{
lean_object* v_unused_1284_; lean_object* v_unused_1285_; 
v_unused_1284_ = lean_ctor_get(v_a_1260_, 1);
lean_dec(v_unused_1284_);
v_unused_1285_ = lean_ctor_get(v_a_1260_, 0);
lean_dec(v_unused_1285_);
v___x_1272_ = v_a_1260_;
v_isShared_1273_ = v_isSharedCheck_1283_;
goto v_resetjp_1271_;
}
else
{
lean_dec(v_a_1260_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1283_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1274_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit___closed__0));
v___x_1275_ = lean_string_append(v___x_1274_, v_a_1265_);
lean_dec(v_a_1265_);
v___x_1276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
lean_ctor_set(v___x_1276_, 1, v_fst_1261_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1276_);
v___x_1278_ = v___x_1272_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_snd_1262_);
v___x_1278_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1280_; 
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v___x_1278_);
v___x_1280_ = v___x_1267_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
else
{
lean_object* v___x_1287_; 
lean_dec(v_a_1265_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v_a_1260_);
v___x_1287_ = v___x_1267_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1260_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec(v_a_1260_);
v_a_1290_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1264_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1264_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_1257_);
return v___x_1259_;
}
}
else
{
uint8_t v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = 0;
v___x_1299_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_e_1250_, v___x_1298_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1309_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1302_ = v___x_1299_;
v_isShared_1303_ = v_isSharedCheck_1309_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1299_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1309_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1304_ = lean_box(0);
v___x_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
lean_ctor_set(v___x_1305_, 1, v_a_1300_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 0, v___x_1305_);
v___x_1307_ = v___x_1302_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
v_a_1310_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1299_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1299_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1250_ = stack[0].m_obj;
lean_object* v_a_1251_ = stack[1].m_obj;
lean_object* v_a_1252_ = stack[2].m_obj;
lean_object* v_a_1253_ = stack[3].m_obj;
lean_object* v_a_1254_ = stack[4].m_obj;
lean_object* v_a_1255_ = stack[5].m_obj;
lean_object* v_res_1318_;
v_res_1318_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(v_e_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
stack->m_obj
 = v_res_1318_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit___boxed(lean_object* v_e_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(v_e_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(lean_object* v_x_1327_, lean_object* v_x_1328_){
_start:
{
if (lean_obj_tag(v_x_1328_) == 0)
{
return v_x_1327_;
}
else
{
lean_object* v_head_1329_; lean_object* v_tail_1330_; lean_object* v___x_1331_; 
v_head_1329_ = lean_ctor_get(v_x_1328_, 0);
v_tail_1330_ = lean_ctor_get(v_x_1328_, 1);
v___x_1331_ = lean_string_append(v_x_1327_, v_head_1329_);
v_x_1327_ = v___x_1331_;
v_x_1328_ = v_tail_1330_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0___boxed(lean_object* v_x_1333_, lean_object* v_x_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(v_x_1333_, v_x_1334_);
lean_dec(v_x_1334_);
return v_res_1335_;
}
}
lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(lean_object* v_e_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(v_e_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1356_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1346_ = v___x_1343_;
v_isShared_1347_ = v_isSharedCheck_1356_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1343_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1356_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v_fst_1348_; lean_object* v_snd_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v_fst_1348_ = lean_ctor_get(v_a_1344_, 0);
lean_inc(v_fst_1348_);
v_snd_1349_ = lean_ctor_get(v_a_1344_, 1);
lean_inc(v_snd_1349_);
lean_dec(v_a_1344_);
v___x_1350_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1351_ = l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(v___x_1350_, v_fst_1348_);
lean_dec(v_fst_1348_);
v___x_1352_ = lean_string_append(v_snd_1349_, v___x_1351_);
lean_dec_ref(v___x_1351_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v___x_1352_);
v___x_1354_ = v___x_1346_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
v_a_1357_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1343_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1343_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1336_ = stack[0].m_obj;
lean_object* v_a_1337_ = stack[1].m_obj;
lean_object* v_a_1338_ = stack[2].m_obj;
lean_object* v_a_1339_ = stack[3].m_obj;
lean_object* v_a_1340_ = stack[4].m_obj;
lean_object* v_a_1341_ = stack[5].m_obj;
lean_object* v_res_1365_;
v_res_1365_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(v_e_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
stack->m_obj
 = v_res_1365_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux___boxed(lean_object* v_e_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(v_e_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
lean_dec(v_a_1371_);
lean_dec_ref(v_a_1370_);
lean_dec(v_a_1369_);
lean_dec_ref(v_a_1368_);
lean_dec(v_a_1367_);
return v_res_1373_;
}
}
lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(lean_object* v_ns_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
switch(lean_obj_tag(v_ns_1374_))
{
case 0:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_box(0);
v___x_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
return v___x_1379_;
}
case 1:
{
lean_object* v_pre_1380_; lean_object* v___x_1381_; lean_object* v_env_1382_; uint8_t v___x_1383_; uint8_t v___x_1384_; 
v_pre_1380_ = lean_ctor_get(v_ns_1374_, 0);
lean_inc(v_pre_1380_);
v___x_1381_ = lean_st_ref_get(v_a_1376_);
v_env_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc_ref(v_env_1382_);
lean_dec(v___x_1381_);
v___x_1383_ = 1;
lean_inc_ref(v_ns_1374_);
v___x_1384_ = l_Lean_Environment_contains(v_env_1382_, v_ns_1374_, v___x_1383_);
if (v___x_1384_ == 0)
{
lean_dec_ref_known(v_ns_1374_, 2);
v_ns_1374_ = v_pre_1380_;
goto _start;
}
else
{
lean_object* v___x_1386_; lean_object* v_seen_1387_; lean_object* v_consts_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1402_; 
v___x_1386_ = lean_st_ref_take(v_a_1375_);
v_seen_1387_ = lean_ctor_get(v___x_1386_, 0);
v_consts_1388_ = lean_ctor_get(v___x_1386_, 1);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1390_ = v___x_1386_;
v_isShared_1391_ = v_isSharedCheck_1402_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_consts_1388_);
lean_inc(v_seen_1387_);
lean_dec(v___x_1386_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1402_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1392_ = lean_box(0);
lean_inc_ref(v_ns_1374_);
v___x_1393_ = l_Lean_Expr_const___override(v_ns_1374_, v___x_1392_);
v___x_1394_ = lean_box(0);
v___x_1395_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(v_seen_1387_, v___x_1393_, v___x_1394_);
v___x_1396_ = l_Lean_NameSet_insert(v_consts_1388_, v_ns_1374_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 1, v___x_1396_);
lean_ctor_set(v___x_1390_, 0, v___x_1395_);
v___x_1398_ = v___x_1390_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1399_; 
v___x_1399_ = lean_st_ref_put(v_a_1375_, v___x_1398_);
v_ns_1374_ = v_pre_1380_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_pre_1403_; 
v_pre_1403_ = lean_ctor_get(v_ns_1374_, 0);
lean_inc(v_pre_1403_);
lean_dec_ref_known(v_ns_1374_, 2);
v_ns_1374_ = v_pre_1403_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ns_1374_ = stack[0].m_obj;
lean_object* v_a_1375_ = stack[1].m_obj;
lean_object* v_a_1376_ = stack[2].m_obj;
lean_object* v_res_1405_;
v_res_1405_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(v_ns_1374_, v_a_1375_, v_a_1376_);
stack->m_obj
 = v_res_1405_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg___boxed(lean_object* v_ns_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(v_ns_1406_, v_a_1407_, v_a_1408_);
lean_dec(v_a_1408_);
lean_dec(v_a_1407_);
return v_res_1410_;
}
}
lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace(lean_object* v_ns_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(v_ns_1411_, v_a_1412_, v_a_1416_);
return v___x_1418_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace_0interp(lean_interpreter_value* stack)
{
lean_object* v_ns_1411_ = stack[0].m_obj;
lean_object* v_a_1412_ = stack[1].m_obj;
lean_object* v_a_1413_ = stack[2].m_obj;
lean_object* v_a_1414_ = stack[3].m_obj;
lean_object* v_a_1415_ = stack[4].m_obj;
lean_object* v_a_1416_ = stack[5].m_obj;
lean_object* v_res_1419_;
v_res_1419_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace(v_ns_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
stack->m_obj
 = v_res_1419_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___boxed(lean_object* v_ns_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace(v_ns_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_);
lean_dec(v_a_1425_);
lean_dec_ref(v_a_1424_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
return v_res_1427_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(lean_object* v_e_1428_, lean_object* v___y_1429_){
_start:
{
uint8_t v___x_1431_; 
v___x_1431_ = l_Lean_Expr_hasMVar(v_e_1428_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v_e_1428_);
return v___x_1432_;
}
else
{
lean_object* v___x_1433_; lean_object* v_mctx_1434_; lean_object* v___x_1435_; lean_object* v_fst_1436_; lean_object* v_snd_1437_; lean_object* v___x_1438_; lean_object* v_cache_1439_; lean_object* v_zetaDeltaFVarIds_1440_; lean_object* v_postponed_1441_; lean_object* v_diag_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1451_; 
v___x_1433_ = lean_st_ref_get(v___y_1429_);
v_mctx_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc_ref(v_mctx_1434_);
lean_dec(v___x_1433_);
v___x_1435_ = l_Lean_instantiateMVarsCore(v_mctx_1434_, v_e_1428_);
v_fst_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_fst_1436_);
v_snd_1437_ = lean_ctor_get(v___x_1435_, 1);
lean_inc(v_snd_1437_);
lean_dec_ref(v___x_1435_);
v___x_1438_ = lean_st_ref_take(v___y_1429_);
v_cache_1439_ = lean_ctor_get(v___x_1438_, 1);
v_zetaDeltaFVarIds_1440_ = lean_ctor_get(v___x_1438_, 2);
v_postponed_1441_ = lean_ctor_get(v___x_1438_, 3);
v_diag_1442_ = lean_ctor_get(v___x_1438_, 4);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1451_ == 0)
{
lean_object* v_unused_1452_; 
v_unused_1452_ = lean_ctor_get(v___x_1438_, 0);
lean_dec(v_unused_1452_);
v___x_1444_ = v___x_1438_;
v_isShared_1445_ = v_isSharedCheck_1451_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_diag_1442_);
lean_inc(v_postponed_1441_);
lean_inc(v_zetaDeltaFVarIds_1440_);
lean_inc(v_cache_1439_);
lean_dec(v___x_1438_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1451_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v_snd_1437_);
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_snd_1437_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_cache_1439_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v_zetaDeltaFVarIds_1440_);
lean_ctor_set(v_reuseFailAlloc_1450_, 3, v_postponed_1441_);
lean_ctor_set(v_reuseFailAlloc_1450_, 4, v_diag_1442_);
v___x_1447_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_st_ref_put(v___y_1429_, v___x_1447_);
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v_fst_1436_);
return v___x_1449_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1428_ = stack[0].m_obj;
lean_object* v___y_1429_ = stack[1].m_obj;
lean_object* v_res_1453_;
v_res_1453_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_1428_, v___y_1429_);
stack->m_obj
 = v_res_1453_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg___boxed(lean_object* v_e_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_1454_, v___y_1455_);
lean_dec(v___y_1455_);
return v_res_1457_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0(lean_object* v_e_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_1458_, v___y_1461_);
return v___x_1465_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1458_ = stack[0].m_obj;
lean_object* v___y_1459_ = stack[1].m_obj;
lean_object* v___y_1460_ = stack[2].m_obj;
lean_object* v___y_1461_ = stack[3].m_obj;
lean_object* v___y_1462_ = stack[4].m_obj;
lean_object* v___y_1463_ = stack[5].m_obj;
lean_object* v_res_1466_;
v_res_1466_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0(v_e_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
stack->m_obj
 = v_res_1466_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___boxed(lean_object* v_e_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0(v_e_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
return v_res_1474_;
}
}
lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(lean_object* v_e_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_){
_start:
{
lean_object* v___x_1482_; lean_object* v_toCold_1483_; lean_object* v_a_1484_; lean_object* v_currNamespace_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1482_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_1475_, v_a_1478_);
v_toCold_1483_ = lean_ctor_get(v_a_1479_, 0);
v_a_1484_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1484_);
lean_dec_ref(v___x_1482_);
v_currNamespace_1485_ = lean_ctor_get(v_toCold_1483_, 4);
lean_inc(v_currNamespace_1485_);
v___x_1486_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(v_currNamespace_1485_, v_a_1476_, v_a_1480_);
lean_dec_ref(v___x_1486_);
v___x_1487_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(v_a_1484_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1489_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
lean_dec_ref_known(v___x_1487_, 1);
v___x_1489_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(v_a_1488_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
return v___x_1489_;
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
v_a_1490_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1487_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1487_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1475_ = stack[0].m_obj;
lean_object* v_a_1476_ = stack[1].m_obj;
lean_object* v_a_1477_ = stack[2].m_obj;
lean_object* v_a_1478_ = stack[3].m_obj;
lean_object* v_a_1479_ = stack[4].m_obj;
lean_object* v_a_1480_ = stack[5].m_obj;
lean_object* v_res_1498_;
v_res_1498_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(v_e_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
stack->m_obj
 = v_res_1498_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName___boxed(lean_object* v_e_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(v_e_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
lean_dec(v_a_1504_);
lean_dec_ref(v_a_1503_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(lean_object* v_x_1508_){
_start:
{
switch(lean_obj_tag(v_x_1508_))
{
case 0:
{
lean_object* v___x_1509_; 
v___x_1509_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
return v___x_1509_;
}
case 1:
{
lean_object* v_pre_1510_; lean_object* v_str_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; uint32_t v___x_1516_; uint32_t v___x_1517_; uint8_t v___x_1518_; 
v_pre_1510_ = lean_ctor_get(v_x_1508_, 0);
lean_inc(v_pre_1510_);
v_str_1511_ = lean_ctor_get(v_x_1508_, 1);
lean_inc_ref(v_str_1511_);
lean_dec_ref_known(v_x_1508_, 2);
v___x_1512_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(v_pre_1510_);
v___x_1513_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix___closed__0));
v___x_1514_ = lean_string_append(v___x_1512_, v___x_1513_);
v___x_1515_ = lean_unsigned_to_nat(0u);
v___x_1516_ = lean_string_utf8_get(v_str_1511_, v___x_1515_);
v___x_1517_ = 65;
v___x_1518_ = lean_uint32_dec_le(v___x_1517_, v___x_1516_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = lean_string_utf8_set(v_str_1511_, v___x_1515_, v___x_1516_);
v___x_1520_ = lean_string_append(v___x_1514_, v___x_1519_);
lean_dec_ref(v___x_1519_);
return v___x_1520_;
}
else
{
uint32_t v___x_1521_; uint8_t v___x_1522_; 
v___x_1521_ = 90;
v___x_1522_ = lean_uint32_dec_le(v___x_1516_, v___x_1521_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = lean_string_utf8_set(v_str_1511_, v___x_1515_, v___x_1516_);
v___x_1524_ = lean_string_append(v___x_1514_, v___x_1523_);
lean_dec_ref(v___x_1523_);
return v___x_1524_;
}
else
{
uint32_t v___x_1525_; uint32_t v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1525_ = 32;
v___x_1526_ = lean_uint32_add(v___x_1516_, v___x_1525_);
v___x_1527_ = lean_string_utf8_set(v_str_1511_, v___x_1515_, v___x_1526_);
v___x_1528_ = lean_string_append(v___x_1514_, v___x_1527_);
lean_dec_ref(v___x_1527_);
return v___x_1528_;
}
}
}
default: 
{
lean_object* v_pre_1529_; 
v_pre_1529_ = lean_ctor_get(v_x_1508_, 0);
lean_inc(v_pre_1529_);
lean_dec_ref_known(v_x_1508_, 2);
v_x_1508_ = v_pre_1529_;
goto _start;
}
}
}
}
lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(lean_object* v___y_1531_){
_start:
{
lean_object* v___x_1533_; lean_object* v_env_1534_; lean_object* v___x_1535_; lean_object* v_mainModule_1536_; lean_object* v___x_1537_; 
v___x_1533_ = lean_st_ref_get(v___y_1531_);
v_env_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc_ref(v_env_1534_);
lean_dec(v___x_1533_);
v___x_1535_ = l_Lean_Environment_header(v_env_1534_);
lean_dec_ref(v_env_1534_);
v_mainModule_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_mainModule_1536_);
lean_dec_ref(v___x_1535_);
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v_mainModule_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT void l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1531_ = stack[0].m_obj;
lean_object* v_res_1538_;
v_res_1538_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v___y_1531_);
stack->m_obj
 = v_res_1538_;
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg___boxed(lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v___y_1539_);
lean_dec(v___y_1539_);
return v_res_1541_;
}
}
lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1(lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v___y_1545_);
return v___x_1547_;
}
}
LEAN_EXPORT void l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1542_ = stack[0].m_obj;
lean_object* v___y_1543_ = stack[1].m_obj;
lean_object* v___y_1544_ = stack[2].m_obj;
lean_object* v___y_1545_ = stack[3].m_obj;
lean_object* v_res_1548_;
v_res_1548_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1(v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
stack->m_obj
 = v_res_1548_;
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___boxed(lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1(v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
return v_res_1554_;
}
}
uint8_t l_instBEqOption_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(lean_object* v_x_1555_, lean_object* v_x_1556_){
_start:
{
if (lean_obj_tag(v_x_1555_) == 0)
{
if (lean_obj_tag(v_x_1556_) == 0)
{
uint8_t v___x_1557_; 
v___x_1557_ = 1;
return v___x_1557_;
}
else
{
uint8_t v___x_1558_; 
v___x_1558_ = 0;
return v___x_1558_;
}
}
else
{
if (lean_obj_tag(v_x_1556_) == 0)
{
uint8_t v___x_1559_; 
v___x_1559_ = 0;
return v___x_1559_;
}
else
{
lean_object* v_val_1560_; lean_object* v_val_1561_; uint8_t v___x_1562_; 
v_val_1560_ = lean_ctor_get(v_x_1555_, 0);
v_val_1561_ = lean_ctor_get(v_x_1556_, 0);
v___x_1562_ = lean_name_eq(v_val_1560_, v_val_1561_);
return v___x_1562_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1555_ = stack[0].m_obj;
lean_object* v_x_1556_ = stack[1].m_obj;
uint8_t v_res_1563_;
v_res_1563_ = l_instBEqOption_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(v_x_1555_, v_x_1556_);
stack->m_num = v_res_1563_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2___boxed(lean_object* v_x_1564_, lean_object* v_x_1565_){
_start:
{
uint8_t v_res_1566_; lean_object* v_r_1567_; 
v_res_1566_ = l_instBEqOption_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(v_x_1564_, v_x_1565_);
lean_dec(v_x_1565_);
lean_dec(v_x_1564_);
v_r_1567_ = lean_box(v_res_1566_);
return v_r_1567_;
}
}
uint8_t l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0(lean_object* v_e_1568_){
_start:
{
if (lean_obj_tag(v_e_1568_) == 4)
{
lean_object* v_declName_1569_; uint8_t v___x_1570_; 
v_declName_1569_ = lean_ctor_get(v_e_1568_, 0);
v___x_1570_ = l_Lean_Name_hasMacroScopes(v_declName_1569_);
return v___x_1570_;
}
else
{
uint8_t v___x_1571_; 
v___x_1571_ = 0;
return v___x_1571_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1568_ = stack[0].m_obj;
uint8_t v_res_1572_;
v_res_1572_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0(v_e_1568_);
stack->m_num = v_res_1572_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0___boxed(lean_object* v_e_1573_){
_start:
{
uint8_t v_res_1574_; lean_object* v_r_1575_; 
v_res_1574_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0(v_e_1573_);
lean_dec_ref(v_e_1573_);
v_r_1575_ = lean_box(v_res_1574_);
return v_r_1575_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(lean_object* v_as_1576_, size_t v_i_1577_, size_t v_stop_1578_){
_start:
{
uint8_t v___x_1579_; 
v___x_1579_ = lean_usize_dec_eq(v_i_1577_, v_stop_1578_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_array_uget_borrowed(v_as_1576_, v_i_1577_);
if (lean_obj_tag(v___x_1580_) == 0)
{
uint8_t v___x_1581_; 
v___x_1581_ = 1;
return v___x_1581_;
}
else
{
size_t v___x_1582_; size_t v___x_1583_; 
v___x_1582_ = ((size_t)1ULL);
v___x_1583_ = lean_usize_add(v_i_1577_, v___x_1582_);
v_i_1577_ = v___x_1583_;
goto _start;
}
}
else
{
uint8_t v___x_1585_; 
v___x_1585_ = 0;
return v___x_1585_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1576_ = stack[0].m_obj;
size_t v_i_1577_ = stack[1].m_num;
size_t v_stop_1578_ = stack[2].m_num;
uint8_t v_res_1586_;
v_res_1586_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(v_as_1576_, v_i_1577_, v_stop_1578_);
stack->m_num = v_res_1586_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5___boxed(lean_object* v_as_1587_, lean_object* v_i_1588_, lean_object* v_stop_1589_){
_start:
{
size_t v_i_boxed_1590_; size_t v_stop_boxed_1591_; uint8_t v_res_1592_; lean_object* v_r_1593_; 
v_i_boxed_1590_ = lean_unbox_usize(v_i_1588_);
lean_dec(v_i_1588_);
v_stop_boxed_1591_ = lean_unbox_usize(v_stop_1589_);
lean_dec(v_stop_1589_);
v_res_1592_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(v_as_1587_, v_i_boxed_1590_, v_stop_boxed_1591_);
lean_dec_ref(v_as_1587_);
v_r_1593_ = lean_box(v_res_1592_);
return v_r_1593_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(lean_object* v___x_1594_, lean_object* v_as_1595_, size_t v_i_1596_, size_t v_stop_1597_){
_start:
{
uint8_t v___x_1598_; 
v___x_1598_ = lean_usize_dec_eq(v_i_1596_, v_stop_1597_);
if (v___x_1598_ == 0)
{
uint8_t v___x_1599_; lean_object* v___y_1601_; lean_object* v___x_1607_; 
v___x_1599_ = 1;
v___x_1607_ = lean_array_uget(v_as_1595_, v_i_1596_);
if (lean_obj_tag(v___x_1607_) == 0)
{
v___y_1601_ = v___x_1607_;
goto v___jp_1600_;
}
else
{
lean_object* v_val_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1616_; 
v_val_1608_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1610_ = v___x_1607_;
v_isShared_1611_ = v_isSharedCheck_1616_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_val_1608_);
lean_dec(v___x_1607_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1616_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1612_ = l_Lean_Name_getRoot(v_val_1608_);
lean_dec(v_val_1608_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v___x_1612_);
v___x_1614_ = v___x_1610_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1612_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
v___y_1601_ = v___x_1614_;
goto v___jp_1600_;
}
}
}
v___jp_1600_:
{
lean_object* v___x_1602_; uint8_t v___x_1603_; 
lean_inc(v___x_1594_);
v___x_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1594_);
v___x_1603_ = l_instBEqOption_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(v___y_1601_, v___x_1602_);
lean_dec_ref_known(v___x_1602_, 1);
lean_dec(v___y_1601_);
if (v___x_1603_ == 0)
{
size_t v___x_1604_; size_t v___x_1605_; 
v___x_1604_ = ((size_t)1ULL);
v___x_1605_ = lean_usize_add(v_i_1596_, v___x_1604_);
v_i_1596_ = v___x_1605_;
goto _start;
}
else
{
lean_dec(v___x_1594_);
return v___x_1599_;
}
}
}
else
{
uint8_t v___x_1617_; 
lean_dec(v___x_1594_);
v___x_1617_ = 0;
return v___x_1617_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1594_ = stack[0].m_obj;
lean_object* v_as_1595_ = stack[1].m_obj;
size_t v_i_1596_ = stack[2].m_num;
size_t v_stop_1597_ = stack[3].m_num;
uint8_t v_res_1618_;
v_res_1618_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(v___x_1594_, v_as_1595_, v_i_1596_, v_stop_1597_);
stack->m_num = v_res_1618_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4___boxed(lean_object* v___x_1619_, lean_object* v_as_1620_, lean_object* v_i_1621_, lean_object* v_stop_1622_){
_start:
{
size_t v_i_boxed_1623_; size_t v_stop_boxed_1624_; uint8_t v_res_1625_; lean_object* v_r_1626_; 
v_i_boxed_1623_ = lean_unbox_usize(v_i_1621_);
lean_dec(v_i_1621_);
v_stop_boxed_1624_ = lean_unbox_usize(v_stop_1622_);
lean_dec(v_stop_1622_);
v_res_1625_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(v___x_1619_, v_as_1620_, v_i_boxed_1623_, v_stop_boxed_1624_);
lean_dec_ref(v_as_1620_);
v_r_1626_ = lean_box(v_res_1625_);
return v_r_1626_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1627_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
return v___x_1629_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1630_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1631_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_1632_ = lean_unsigned_to_nat(0u);
v___x_1633_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
lean_ctor_set(v___x_1633_, 2, v___x_1632_);
lean_ctor_set(v___x_1633_, 3, v___x_1632_);
lean_ctor_set(v___x_1633_, 4, v___x_1631_);
lean_ctor_set(v___x_1633_, 5, v___x_1631_);
lean_ctor_set(v___x_1633_, 6, v___x_1631_);
lean_ctor_set(v___x_1633_, 7, v___x_1631_);
lean_ctor_set(v___x_1633_, 8, v___x_1631_);
lean_ctor_set(v___x_1633_, 9, v___x_1631_);
lean_ctor_set(v___x_1633_, 10, v___x_1631_);
lean_ctor_set(v___x_1633_, 11, v___x_1630_);
return v___x_1633_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1634_ = lean_unsigned_to_nat(32u);
v___x_1635_ = lean_mk_empty_array_with_capacity(v___x_1634_);
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
return v___x_1636_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1637_ = ((size_t)5ULL);
v___x_1638_ = lean_unsigned_to_nat(0u);
v___x_1639_ = lean_unsigned_to_nat(32u);
v___x_1640_ = lean_mk_empty_array_with_capacity(v___x_1639_);
v___x_1641_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_1642_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v___x_1640_);
lean_ctor_set(v___x_1642_, 2, v___x_1638_);
lean_ctor_set(v___x_1642_, 3, v___x_1638_);
lean_ctor_set_usize(v___x_1642_, 4, v___x_1637_);
return v___x_1642_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1643_ = lean_box(1);
v___x_1644_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_1645_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_1646_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
lean_ctor_set(v___x_1646_, 1, v___x_1644_);
lean_ctor_set(v___x_1646_, 2, v___x_1643_);
return v___x_1646_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_1649_ = l_Lean_stringToMessageData(v___x_1648_);
return v___x_1649_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_1652_ = l_Lean_stringToMessageData(v___x_1651_);
return v___x_1652_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_1655_ = l_Lean_stringToMessageData(v___x_1654_);
return v___x_1655_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_1658_ = l_Lean_stringToMessageData(v___x_1657_);
return v___x_1658_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__14));
v___x_1661_ = l_Lean_stringToMessageData(v___x_1660_);
return v___x_1661_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1663_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__16));
v___x_1664_ = l_Lean_stringToMessageData(v___x_1663_);
return v___x_1664_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__18));
v___x_1667_ = l_Lean_stringToMessageData(v___x_1666_);
return v___x_1667_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__21(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__20));
v___x_1670_ = l_Lean_stringToMessageData(v___x_1669_);
return v___x_1670_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__23(void){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__22));
v___x_1673_ = l_Lean_stringToMessageData(v___x_1672_);
return v___x_1673_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__25(void){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__24));
v___x_1676_ = l_Lean_stringToMessageData(v___x_1675_);
return v___x_1676_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__27(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__26));
v___x_1679_ = l_Lean_stringToMessageData(v___x_1678_);
return v___x_1679_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_1680_, lean_object* v_declHint_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v_env_1686_; uint8_t v___x_1687_; 
v___x_1684_ = lean_box(0);
v___x_1685_ = lean_st_ref_get(v___y_1682_);
v_env_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc_ref(v_env_1686_);
lean_dec(v___x_1685_);
v___x_1687_ = l_Lean_Name_isAnonymous(v_declHint_1681_);
if (v___x_1687_ == 0)
{
uint8_t v_isExporting_1688_; 
v_isExporting_1688_ = lean_ctor_get_uint8(v_env_1686_, sizeof(void*)*13);
if (v_isExporting_1688_ == 0)
{
lean_object* v___x_1689_; 
lean_dec_ref(v_env_1686_);
lean_dec(v_declHint_1681_);
v___x_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1689_, 0, v_msg_1680_);
return v___x_1689_;
}
else
{
lean_object* v___x_1690_; uint8_t v___x_1691_; 
lean_inc_ref(v_env_1686_);
v___x_1690_ = l_Lean_Environment_setExporting(v_env_1686_, v___x_1687_);
lean_inc(v_declHint_1681_);
lean_inc_ref(v___x_1690_);
v___x_1691_ = l_Lean_Environment_contains(v___x_1690_, v_declHint_1681_, v_isExporting_1688_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; 
lean_dec_ref(v___x_1690_);
lean_dec_ref(v_env_1686_);
lean_dec(v_declHint_1681_);
v___x_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1692_, 0, v_msg_1680_);
return v___x_1692_;
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v_c_1698_; lean_object* v___x_1699_; 
v___x_1693_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_1694_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5);
v___x_1695_ = l_Lean_Options_empty;
v___x_1696_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1690_);
lean_ctor_set(v___x_1696_, 1, v___x_1693_);
lean_ctor_set(v___x_1696_, 2, v___x_1694_);
lean_ctor_set(v___x_1696_, 3, v___x_1695_);
lean_inc(v_declHint_1681_);
v___x_1697_ = l_Lean_MessageData_ofConstName(v_declHint_1681_, v___x_1687_);
v_c_1698_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1698_, 0, v___x_1696_);
lean_ctor_set(v_c_1698_, 1, v___x_1697_);
v___x_1699_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1686_, v_declHint_1681_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_dec_ref(v_env_1686_);
lean_dec(v_declHint_1681_);
v___x_1700_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_1701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1700_);
lean_ctor_set(v___x_1701_, 1, v_c_1698_);
v___x_1702_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9);
v___x_1703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1701_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = l_Lean_MessageData_note(v___x_1703_);
v___x_1705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1705_, 0, v_msg_1680_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1705_);
return v___x_1706_;
}
else
{
lean_object* v_val_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1763_; 
v_val_1707_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1709_ = v___x_1699_;
v_isShared_1710_ = v_isSharedCheck_1763_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_val_1707_);
lean_dec(v___x_1699_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1763_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1711_; lean_object* v_modules_1712_; lean_object* v_moduleNames_1713_; lean_object* v_mod_1714_; uint8_t v___y_1716_; uint8_t v___x_1746_; 
v___x_1711_ = l_Lean_Environment_header(v_env_1686_);
lean_dec_ref(v_env_1686_);
v_modules_1712_ = lean_ctor_get(v___x_1711_, 3);
lean_inc_ref(v_modules_1712_);
v_moduleNames_1713_ = lean_ctor_get(v___x_1711_, 4);
lean_inc_ref(v_moduleNames_1713_);
lean_dec_ref(v___x_1711_);
v_mod_1714_ = lean_array_get(v___x_1684_, v_moduleNames_1713_, v_val_1707_);
lean_dec_ref(v_moduleNames_1713_);
v___x_1746_ = l_Lean_isPrivateName(v_declHint_1681_);
lean_dec(v_declHint_1681_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1747_ = lean_array_get_size(v_modules_1712_);
v___x_1748_ = lean_nat_dec_lt(v_val_1707_, v___x_1747_);
if (v___x_1748_ == 0)
{
lean_dec_ref(v_modules_1712_);
lean_dec(v_val_1707_);
v___y_1716_ = v___x_1746_;
goto v___jp_1715_;
}
else
{
lean_object* v___x_1749_; lean_object* v_toImport_1750_; uint8_t v_isExported_1751_; 
v___x_1749_ = lean_array_fget(v_modules_1712_, v_val_1707_);
lean_dec(v_val_1707_);
lean_dec_ref(v_modules_1712_);
v_toImport_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc_ref(v_toImport_1750_);
lean_dec(v___x_1749_);
v_isExported_1751_ = lean_ctor_get_uint8(v_toImport_1750_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1750_);
v___y_1716_ = v_isExported_1751_;
goto v___jp_1715_;
}
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
lean_dec_ref(v_modules_1712_);
lean_del_object(v___x_1709_);
lean_dec(v_val_1707_);
v___x_1752_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_1753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
lean_ctor_set(v___x_1753_, 1, v_c_1698_);
v___x_1754_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__25);
v___x_1755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1753_);
lean_ctor_set(v___x_1755_, 1, v___x_1754_);
v___x_1756_ = l_Lean_MessageData_ofName(v_mod_1714_);
v___x_1757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1755_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
v___x_1758_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__27);
v___x_1759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1757_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v___x_1760_ = l_Lean_MessageData_note(v___x_1759_);
v___x_1761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1761_, 0, v_msg_1680_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
return v___x_1762_;
}
v___jp_1715_:
{
if (v___y_1716_ == 0)
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1717_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_1718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
lean_ctor_set(v___x_1718_, 1, v_c_1698_);
v___x_1719_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_1720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1718_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
v___x_1721_ = l_Lean_MessageData_ofName(v_mod_1714_);
v___x_1722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1720_);
lean_ctor_set(v___x_1722_, 1, v___x_1721_);
v___x_1723_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_1724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1722_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
v___x_1725_ = l_Lean_MessageData_note(v___x_1724_);
v___x_1726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1726_, 0, v_msg_1680_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set_tag(v___x_1709_, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1726_);
v___x_1728_ = v___x_1709_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
else
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1730_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17);
v___x_1731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
lean_ctor_set(v___x_1731_, 1, v_c_1698_);
v___x_1732_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19);
v___x_1733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1731_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = l_Lean_MessageData_ofName(v_mod_1714_);
lean_inc_ref(v___x_1734_);
v___x_1735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1733_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
v___x_1736_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__21);
v___x_1737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1735_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
v___x_1738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
lean_ctor_set(v___x_1738_, 1, v___x_1734_);
v___x_1739_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__23);
v___x_1740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1738_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
v___x_1741_ = l_Lean_MessageData_note(v___x_1740_);
v___x_1742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1742_, 0, v_msg_1680_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set_tag(v___x_1709_, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1742_);
v___x_1744_ = v___x_1709_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
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
lean_object* v___x_1764_; 
lean_dec_ref(v_env_1686_);
lean_dec(v_declHint_1681_);
v___x_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1764_, 0, v_msg_1680_);
return v___x_1764_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1680_ = stack[0].m_obj;
lean_object* v_declHint_1681_ = stack[1].m_obj;
lean_object* v___y_1682_ = stack[2].m_obj;
lean_object* v_res_1765_;
v_res_1765_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_1680_, v_declHint_1681_, v___y_1682_);
stack->m_obj
 = v_res_1765_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_1766_, lean_object* v_declHint_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_1766_, v_declHint_1767_, v___y_1768_);
lean_dec(v___y_1768_);
return v_res_1770_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(lean_object* v_msg_1771_, lean_object* v_declHint_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v___x_1778_; lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1788_; 
v___x_1778_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_1771_, v_declHint_1772_, v___y_1776_);
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1781_ = v___x_1778_;
v_isShared_1782_ = v_isSharedCheck_1788_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1778_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1788_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
v___x_1783_ = l_Lean_unknownIdentifierMessageTag;
v___x_1784_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
lean_ctor_set(v___x_1784_, 1, v_a_1779_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1784_);
v___x_1786_ = v___x_1781_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1771_ = stack[0].m_obj;
lean_object* v_declHint_1772_ = stack[1].m_obj;
lean_object* v___y_1773_ = stack[2].m_obj;
lean_object* v___y_1774_ = stack[3].m_obj;
lean_object* v___y_1775_ = stack[4].m_obj;
lean_object* v___y_1776_ = stack[5].m_obj;
lean_object* v_res_1789_;
v_res_1789_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(v_msg_1771_, v_declHint_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
stack->m_obj
 = v_res_1789_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1790_, lean_object* v_declHint_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(v_msg_1790_, v_declHint_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
return v_res_1797_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(lean_object* v_ref_1798_, lean_object* v_msg_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_toCold_1805_; lean_object* v_currRecDepth_1806_; lean_object* v_ref_1807_; uint16_t v_optionFlags_1808_; uint8_t v_suppressElabErrors_1809_; uint8_t v_isRecordingDeps_1810_; lean_object* v_ref_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v_toCold_1805_ = lean_ctor_get(v___y_1802_, 0);
v_currRecDepth_1806_ = lean_ctor_get(v___y_1802_, 1);
v_ref_1807_ = lean_ctor_get(v___y_1802_, 2);
v_optionFlags_1808_ = lean_ctor_get_uint16(v___y_1802_, sizeof(void*)*3);
v_suppressElabErrors_1809_ = lean_ctor_get_uint8(v___y_1802_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1810_ = lean_ctor_get_uint8(v___y_1802_, sizeof(void*)*3 + 3);
v_ref_1811_ = l_Lean_replaceRef(v_ref_1798_, v_ref_1807_);
lean_inc(v_currRecDepth_1806_);
lean_inc_ref(v_toCold_1805_);
v___x_1812_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1812_, 0, v_toCold_1805_);
lean_ctor_set(v___x_1812_, 1, v_currRecDepth_1806_);
lean_ctor_set(v___x_1812_, 2, v_ref_1811_);
lean_ctor_set_uint16(v___x_1812_, sizeof(void*)*3, v_optionFlags_1808_);
lean_ctor_set_uint8(v___x_1812_, sizeof(void*)*3 + 2, v_suppressElabErrors_1809_);
lean_ctor_set_uint8(v___x_1812_, sizeof(void*)*3 + 3, v_isRecordingDeps_1810_);
v___x_1813_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v_msg_1799_, v___y_1800_, v___y_1801_, v___x_1812_, v___y_1803_);
lean_dec_ref_known(v___x_1812_, 3);
return v___x_1813_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1798_ = stack[0].m_obj;
lean_object* v_msg_1799_ = stack[1].m_obj;
lean_object* v___y_1800_ = stack[2].m_obj;
lean_object* v___y_1801_ = stack[3].m_obj;
lean_object* v___y_1802_ = stack[4].m_obj;
lean_object* v___y_1803_ = stack[5].m_obj;
lean_object* v_res_1814_;
v_res_1814_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_1798_, v_msg_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
stack->m_obj
 = v_res_1814_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_ref_1815_, lean_object* v_msg_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_1815_, v_msg_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v_ref_1815_);
return v_res_1822_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(lean_object* v_ref_1823_, lean_object* v_msg_1824_, lean_object* v_declHint_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v___x_1831_; lean_object* v_a_1832_; lean_object* v___x_1833_; 
v___x_1831_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(v_msg_1824_, v_declHint_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref(v___x_1831_);
v___x_1833_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_1823_, v_a_1832_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
return v___x_1833_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1823_ = stack[0].m_obj;
lean_object* v_msg_1824_ = stack[1].m_obj;
lean_object* v_declHint_1825_ = stack[2].m_obj;
lean_object* v___y_1826_ = stack[3].m_obj;
lean_object* v___y_1827_ = stack[4].m_obj;
lean_object* v___y_1828_ = stack[5].m_obj;
lean_object* v___y_1829_ = stack[6].m_obj;
lean_object* v_res_1834_;
v_res_1834_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_1823_, v_msg_1824_, v_declHint_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
stack->m_obj
 = v_res_1834_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg___boxed(lean_object* v_ref_1835_, lean_object* v_msg_1836_, lean_object* v_declHint_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_1835_, v_msg_1836_, v_declHint_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v_ref_1835_);
return v_res_1843_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__0));
v___x_1846_ = l_Lean_stringToMessageData(v___x_1845_);
return v___x_1846_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__2));
v___x_1849_ = l_Lean_stringToMessageData(v___x_1848_);
return v___x_1849_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_ref_1850_, lean_object* v_constName_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v___x_1857_; uint8_t v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1857_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1);
v___x_1858_ = 0;
lean_inc(v_constName_1851_);
v___x_1859_ = l_Lean_MessageData_ofConstName(v_constName_1851_, v___x_1858_);
v___x_1860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1857_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3);
v___x_1862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1860_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_1850_, v___x_1862_, v_constName_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
return v___x_1863_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1850_ = stack[0].m_obj;
lean_object* v_constName_1851_ = stack[1].m_obj;
lean_object* v___y_1852_ = stack[2].m_obj;
lean_object* v___y_1853_ = stack[3].m_obj;
lean_object* v___y_1854_ = stack[4].m_obj;
lean_object* v___y_1855_ = stack[5].m_obj;
lean_object* v_res_1864_;
v_res_1864_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1850_, v_constName_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
stack->m_obj
 = v_res_1864_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v_ref_1865_, lean_object* v_constName_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1865_, v_constName_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v_ref_1865_);
return v_res_1872_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(lean_object* v_constName_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_ref_1879_; lean_object* v___x_1880_; 
v_ref_1879_ = lean_ctor_get(v___y_1876_, 2);
v___x_1880_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1879_, v_constName_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
return v___x_1880_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1873_ = stack[0].m_obj;
lean_object* v___y_1874_ = stack[1].m_obj;
lean_object* v___y_1875_ = stack[2].m_obj;
lean_object* v___y_1876_ = stack[3].m_obj;
lean_object* v___y_1877_ = stack[4].m_obj;
lean_object* v_res_1881_;
v_res_1881_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
stack->m_obj
 = v_res_1881_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_constName_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
return v_res_1888_;
}
}
lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(lean_object* v_constName_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; lean_object* v_env_1896_; uint8_t v___x_1897_; lean_object* v___x_1898_; 
v___x_1895_ = lean_st_ref_get(v___y_1893_);
v_env_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc_ref(v_env_1896_);
lean_dec(v___x_1895_);
v___x_1897_ = 0;
lean_inc(v_constName_1889_);
v___x_1898_ = l_Lean_Environment_find_x3f(v_env_1896_, v_constName_1889_, v___x_1897_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
return v___x_1899_;
}
else
{
lean_object* v_val_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
lean_dec(v_constName_1889_);
v_val_1900_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1898_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_val_1900_);
lean_dec(v___x_1898_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set_tag(v___x_1902_, 0);
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_val_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1889_ = stack[0].m_obj;
lean_object* v___y_1890_ = stack[1].m_obj;
lean_object* v___y_1891_ = stack[2].m_obj;
lean_object* v___y_1892_ = stack[3].m_obj;
lean_object* v___y_1893_ = stack[4].m_obj;
lean_object* v_res_1908_;
v_res_1908_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(v_constName_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
stack->m_obj
 = v_res_1908_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0___boxed(lean_object* v_constName_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(v_constName_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
return v_res_1915_;
}
}
lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(lean_object* v_declName_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = lean_box(0);
lean_inc(v_declName_1916_);
v___x_1923_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(v_declName_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1949_; 
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1949_ == 0)
{
lean_object* v_unused_1950_; 
v_unused_1950_ = lean_ctor_get(v___x_1923_, 0);
lean_dec(v_unused_1950_);
v___x_1925_ = v___x_1923_;
v_isShared_1926_ = v_isSharedCheck_1949_;
goto v_resetjp_1924_;
}
else
{
lean_dec(v___x_1923_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1949_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1927_; lean_object* v_env_1928_; lean_object* v___x_1929_; 
v___x_1927_ = lean_st_ref_get(v___y_1920_);
v_env_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc_ref(v_env_1928_);
lean_dec(v___x_1927_);
v___x_1929_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1928_, v_declName_1916_);
lean_dec(v_declName_1916_);
lean_dec_ref(v_env_1928_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v___x_1930_; lean_object* v___x_1932_; 
v___x_1930_ = lean_box(0);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 0, v___x_1930_);
v___x_1932_ = v___x_1925_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
else
{
lean_object* v_val_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1948_; 
v_val_1934_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1936_ = v___x_1929_;
v_isShared_1937_ = v_isSharedCheck_1948_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_val_1934_);
lean_dec(v___x_1929_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1948_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1938_; lean_object* v_env_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1943_; 
v___x_1938_ = lean_st_ref_get(v___y_1920_);
v_env_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc_ref(v_env_1939_);
lean_dec(v___x_1938_);
v___x_1940_ = l_Lean_Environment_allImportedModuleNames(v_env_1939_);
lean_dec_ref(v_env_1939_);
v___x_1941_ = lean_array_get(v___x_1922_, v___x_1940_, v_val_1934_);
lean_dec(v_val_1934_);
lean_dec_ref(v___x_1940_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v___x_1941_);
v___x_1943_ = v___x_1936_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1941_);
v___x_1943_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
lean_object* v___x_1945_; 
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 0, v___x_1943_);
v___x_1945_ = v___x_1925_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_dec(v_declName_1916_);
v_a_1951_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1923_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1923_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1916_ = stack[0].m_obj;
lean_object* v___y_1917_ = stack[1].m_obj;
lean_object* v___y_1918_ = stack[2].m_obj;
lean_object* v___y_1919_ = stack[3].m_obj;
lean_object* v___y_1920_ = stack[4].m_obj;
lean_object* v_res_1959_;
v_res_1959_ = l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(v_declName_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
stack->m_obj
 = v_res_1959_;
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0___boxed(lean_object* v_declName_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(v_declName_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
return v_res_1966_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(lean_object* v_init_1967_, lean_object* v_x_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
if (lean_obj_tag(v_x_1968_) == 0)
{
lean_object* v_k_1974_; lean_object* v_l_1975_; lean_object* v_r_1976_; lean_object* v___x_1977_; 
v_k_1974_ = lean_ctor_get(v_x_1968_, 1);
lean_inc(v_k_1974_);
v_l_1975_ = lean_ctor_get(v_x_1968_, 3);
lean_inc(v_l_1975_);
v_r_1976_ = lean_ctor_get(v_x_1968_, 4);
lean_inc(v_r_1976_);
lean_dec_ref_known(v_x_1968_, 5);
v___x_1977_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v_init_1967_, v_l_1975_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1979_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref_known(v___x_1977_, 1);
v___x_1979_ = l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(v_k_1974_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1981_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___x_1979_, 1);
v___x_1981_ = lean_array_push(v_a_1978_, v_a_1980_);
v_init_1967_ = v___x_1981_;
v_x_1968_ = v_r_1976_;
goto _start;
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec(v_a_1978_);
lean_dec(v_r_1976_);
v_a_1983_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1979_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1979_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
else
{
lean_dec(v_r_1976_);
lean_dec(v_k_1974_);
return v___x_1977_;
}
}
else
{
lean_object* v___x_1991_; 
v___x_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1991_, 0, v_init_1967_);
return v___x_1991_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1967_ = stack[0].m_obj;
lean_object* v_x_1968_ = stack[1].m_obj;
lean_object* v___y_1969_ = stack[2].m_obj;
lean_object* v___y_1970_ = stack[3].m_obj;
lean_object* v___y_1971_ = stack[4].m_obj;
lean_object* v___y_1972_ = stack[5].m_obj;
lean_object* v_res_1992_;
v_res_1992_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v_init_1967_, v_x_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
stack->m_obj
 = v_res_1992_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3___boxed(lean_object* v_init_1993_, lean_object* v_x_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v_init_1993_, v_x_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
return v_res_2000_;
}
}
static lean_object* _init_l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1(void){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2002_ = l_Lean_NameSet_empty;
v___x_2003_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1);
v___x_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
lean_ctor_set(v___x_2004_, 1, v___x_2002_);
return v___x_2004_;
}
}
lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(lean_object* v_pre_2005_, lean_object* v_type_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v___f_2012_; lean_object* v___y_2014_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___f_2012_ = ((lean_object*)(l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0));
v___x_2020_ = lean_unsigned_to_nat(0u);
v___x_2021_ = lean_obj_once(&l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1, &l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1_once, _init_l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1);
v___x_2022_ = lean_st_mk_ref(v___x_2021_);
lean_inc_ref(v_type_2006_);
v___x_2023_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(v_type_2006_, v___x_2022_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v_a_2028_; lean_object* v_consts_2029_; lean_object* v___x_2030_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2042_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
v___x_2025_ = lean_st_ref_get(v___x_2022_);
lean_dec(v___x_2022_);
v___x_2026_ = lean_string_append(v_pre_2005_, v_a_2024_);
lean_dec(v_a_2024_);
v___x_2027_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v_a_2010_);
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref(v___x_2027_);
v_consts_2029_ = lean_ctor_get(v___x_2025_, 1);
lean_inc(v_consts_2029_);
lean_dec(v___x_2025_);
v___x_2030_ = l_Lean_Name_getRoot(v_a_2028_);
lean_dec(v_a_2028_);
if (lean_obj_tag(v_consts_2029_) == 0)
{
lean_object* v_size_2059_; 
v_size_2059_ = lean_ctor_get(v_consts_2029_, 0);
lean_inc(v_size_2059_);
v___y_2042_ = v_size_2059_;
goto v___jp_2041_;
}
else
{
v___y_2042_ = v___x_2020_;
goto v___jp_2041_;
}
v___jp_2031_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(v___x_2030_);
v___x_2033_ = lean_string_append(v___x_2026_, v___x_2032_);
lean_dec_ref(v___x_2032_);
v___y_2014_ = v___x_2033_;
goto v___jp_2013_;
}
v___jp_2034_:
{
uint8_t v___x_2037_; 
v___x_2037_ = lean_nat_dec_lt(v___x_2020_, v___y_2035_);
if (v___x_2037_ == 0)
{
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
goto v___jp_2031_;
}
else
{
if (v___x_2037_ == 0)
{
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
goto v___jp_2031_;
}
else
{
size_t v___x_2038_; size_t v___x_2039_; uint8_t v___x_2040_; 
v___x_2038_ = ((size_t)0ULL);
v___x_2039_ = lean_usize_of_nat(v___y_2035_);
lean_dec(v___y_2035_);
lean_inc(v___x_2030_);
v___x_2040_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(v___x_2030_, v___y_2036_, v___x_2038_, v___x_2039_);
lean_dec_ref(v___y_2036_);
if (v___x_2040_ == 0)
{
goto v___jp_2031_;
}
else
{
lean_dec(v___x_2030_);
v___y_2014_ = v___x_2026_;
goto v___jp_2013_;
}
}
}
}
v___jp_2041_:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = lean_mk_empty_array_with_capacity(v___y_2042_);
lean_dec(v___y_2042_);
v___x_2044_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v___x_2043_, v_consts_2029_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref_known(v___x_2044_, 1);
v___x_2046_ = lean_array_get_size(v_a_2045_);
v___x_2047_ = lean_nat_dec_lt(v___x_2020_, v___x_2046_);
if (v___x_2047_ == 0)
{
v___y_2035_ = v___x_2046_;
v___y_2036_ = v_a_2045_;
goto v___jp_2034_;
}
else
{
if (v___x_2047_ == 0)
{
v___y_2035_ = v___x_2046_;
v___y_2036_ = v_a_2045_;
goto v___jp_2034_;
}
else
{
size_t v___x_2048_; size_t v___x_2049_; uint8_t v___x_2050_; 
v___x_2048_ = ((size_t)0ULL);
v___x_2049_ = lean_usize_of_nat(v___x_2046_);
v___x_2050_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(v_a_2045_, v___x_2048_, v___x_2049_);
if (v___x_2050_ == 0)
{
v___y_2035_ = v___x_2046_;
v___y_2036_ = v_a_2045_;
goto v___jp_2034_;
}
else
{
lean_dec(v_a_2045_);
lean_dec(v___x_2030_);
v___y_2014_ = v___x_2026_;
goto v___jp_2013_;
}
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v___x_2030_);
lean_dec_ref(v___x_2026_);
lean_dec_ref(v_type_2006_);
v_a_2051_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2044_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2044_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec(v___x_2022_);
lean_dec_ref(v_type_2006_);
lean_dec_ref(v_pre_2005_);
v_a_2060_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2023_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2023_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
v___jp_2013_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2015_ = lean_box(0);
v___x_2016_ = l_Lean_Name_str___override(v___x_2015_, v___y_2014_);
v___x_2017_ = lean_find_expr(v___f_2012_, v_type_2006_);
lean_dec_ref(v_type_2006_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v___x_2018_; 
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2016_);
return v___x_2018_;
}
else
{
lean_object* v___x_2019_; 
lean_dec_ref_known(v___x_2017_, 1);
v___x_2019_ = l_Lean_Core_mkFreshUserName(v___x_2016_, v_a_2009_, v_a_2010_);
return v___x_2019_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2005_ = stack[0].m_obj;
lean_object* v_type_2006_ = stack[1].m_obj;
lean_object* v_a_2007_ = stack[2].m_obj;
lean_object* v_a_2008_ = stack[3].m_obj;
lean_object* v_a_2009_ = stack[4].m_obj;
lean_object* v_a_2010_ = stack[5].m_obj;
lean_object* v_res_2068_;
v_res_2068_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(v_pre_2005_, v_type_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
stack->m_obj
 = v_res_2068_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___boxed(lean_object* v_pre_2069_, lean_object* v_type_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(v_pre_2069_, v_type_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
lean_dec(v_a_2074_);
lean_dec_ref(v_a_2073_);
lean_dec(v_a_2072_);
lean_dec_ref(v_a_2071_);
return v_res_2076_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_2077_, lean_object* v_constName_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
return v___x_2084_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2078_ = stack[1].m_obj;
lean_object* v___y_2079_ = stack[2].m_obj;
lean_object* v___y_2080_ = stack[3].m_obj;
lean_object* v___y_2081_ = stack[4].m_obj;
lean_object* v___y_2082_ = stack[5].m_obj;
lean_object* v_res_2085_;
v_res_2085_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3(lean_box(0), v_constName_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
stack->m_obj
 = v_res_2085_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_2086_, lean_object* v_constName_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3(v_00_u03b1_2086_, v_constName_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
return v_res_2093_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b1_2094_, lean_object* v_ref_2095_, lean_object* v_constName_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_2095_, v_constName_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
return v___x_2102_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2095_ = stack[1].m_obj;
lean_object* v_constName_2096_ = stack[2].m_obj;
lean_object* v___y_2097_ = stack[3].m_obj;
lean_object* v___y_2098_ = stack[4].m_obj;
lean_object* v___y_2099_ = stack[5].m_obj;
lean_object* v___y_2100_ = stack[6].m_obj;
lean_object* v_res_2103_;
v_res_2103_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7(lean_box(0), v_ref_2095_, v_constName_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
stack->m_obj
 = v_res_2103_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_00_u03b1_2104_, lean_object* v_ref_2105_, lean_object* v_constName_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7(v_00_u03b1_2104_, v_ref_2105_, v_constName_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v_ref_2105_);
return v_res_2112_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8(lean_object* v_00_u03b1_2113_, lean_object* v_ref_2114_, lean_object* v_msg_2115_, lean_object* v_declHint_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_2114_, v_msg_2115_, v_declHint_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
return v___x_2122_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2114_ = stack[1].m_obj;
lean_object* v_msg_2115_ = stack[2].m_obj;
lean_object* v_declHint_2116_ = stack[3].m_obj;
lean_object* v___y_2117_ = stack[4].m_obj;
lean_object* v___y_2118_ = stack[5].m_obj;
lean_object* v___y_2119_ = stack[6].m_obj;
lean_object* v___y_2120_ = stack[7].m_obj;
lean_object* v_res_2123_;
v_res_2123_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8(lean_box(0), v_ref_2114_, v_msg_2115_, v_declHint_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
stack->m_obj
 = v_res_2123_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___boxed(lean_object* v_00_u03b1_2124_, lean_object* v_ref_2125_, lean_object* v_msg_2126_, lean_object* v_declHint_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8(v_00_u03b1_2124_, v_ref_2125_, v_msg_2126_, v_declHint_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v_ref_2125_);
return v_res_2133_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10(lean_object* v_msg_2134_, lean_object* v_declHint_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v___x_2141_; 
v___x_2141_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_2134_, v_declHint_2135_, v___y_2139_);
return v___x_2141_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2134_ = stack[0].m_obj;
lean_object* v_declHint_2135_ = stack[1].m_obj;
lean_object* v___y_2136_ = stack[2].m_obj;
lean_object* v___y_2137_ = stack[3].m_obj;
lean_object* v___y_2138_ = stack[4].m_obj;
lean_object* v___y_2139_ = stack[5].m_obj;
lean_object* v_res_2142_;
v_res_2142_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10(v_msg_2134_, v_declHint_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
stack->m_obj
 = v_res_2142_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_2143_, lean_object* v_declHint_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10(v_msg_2143_, v_declHint_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
return v_res_2150_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_2151_, lean_object* v_ref_2152_, lean_object* v_msg_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_2152_, v_msg_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
return v___x_2159_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2152_ = stack[1].m_obj;
lean_object* v_msg_2153_ = stack[2].m_obj;
lean_object* v___y_2154_ = stack[3].m_obj;
lean_object* v___y_2155_ = stack[4].m_obj;
lean_object* v___y_2156_ = stack[5].m_obj;
lean_object* v___y_2157_ = stack[6].m_obj;
lean_object* v_res_2160_;
v_res_2160_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10(lean_box(0), v_ref_2152_, v_msg_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
stack->m_obj
 = v_res_2160_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_2161_, lean_object* v_ref_2162_, lean_object* v_msg_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10(v_00_u03b1_2161_, v_ref_2162_, v_msg_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v_ref_2162_);
return v_res_2169_;
}
}
lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg(lean_object* v_a_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
return v___x_2178_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2170_ = stack[0].m_obj;
lean_object* v___y_2171_ = stack[1].m_obj;
lean_object* v___y_2172_ = stack[2].m_obj;
lean_object* v___y_2173_ = stack[3].m_obj;
lean_object* v___y_2174_ = stack[4].m_obj;
lean_object* v___y_2175_ = stack[5].m_obj;
lean_object* v___y_2176_ = stack[6].m_obj;
lean_object* v_res_2179_;
v_res_2179_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg(v_a_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
stack->m_obj
 = v_res_2179_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg___boxed(lean_object* v_a_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg(v_a_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
return v_res_2188_;
}
}
lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0(lean_object* v_00_u03b1_2189_, lean_object* v_a_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
return v___x_2198_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2190_ = stack[1].m_obj;
lean_object* v___y_2191_ = stack[2].m_obj;
lean_object* v___y_2192_ = stack[3].m_obj;
lean_object* v___y_2193_ = stack[4].m_obj;
lean_object* v___y_2194_ = stack[5].m_obj;
lean_object* v___y_2195_ = stack[6].m_obj;
lean_object* v___y_2196_ = stack[7].m_obj;
lean_object* v_res_2199_;
v_res_2199_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0(lean_box(0), v_a_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
stack->m_obj
 = v_res_2199_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___boxed(lean_object* v_00_u03b1_2200_, lean_object* v_a_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0(v_00_u03b1_2200_, v_a_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
return v_res_2209_;
}
}
lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0(lean_object* v_type_2210_, lean_object* v_binds_2211_, lean_object* v_pre_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Lean_Elab_Term_elabType(v_type_2210_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; uint8_t v___x_2222_; uint8_t v___x_2223_; uint8_t v___x_2224_; lean_object* v___x_2225_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
lean_dec_ref_known(v___x_2220_, 1);
v___x_2222_ = 0;
v___x_2223_ = 1;
v___x_2224_ = 1;
v___x_2225_ = l_Lean_Meta_mkForallFVars(v_binds_2211_, v_a_2221_, v___x_2222_, v___x_2223_, v___x_2223_, v___x_2224_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2227_; 
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_a_2226_);
lean_dec_ref_known(v___x_2225_, 1);
v___x_2227_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(v_pre_2212_, v_a_2226_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
return v___x_2227_;
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec_ref(v_pre_2212_);
v_a_2228_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2225_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2225_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec_ref(v_pre_2212_);
v_a_2236_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2220_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2220_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2210_ = stack[0].m_obj;
lean_object* v_binds_2211_ = stack[1].m_obj;
lean_object* v_pre_2212_ = stack[2].m_obj;
lean_object* v___y_2213_ = stack[3].m_obj;
lean_object* v___y_2214_ = stack[4].m_obj;
lean_object* v___y_2215_ = stack[5].m_obj;
lean_object* v___y_2216_ = stack[6].m_obj;
lean_object* v___y_2217_ = stack[7].m_obj;
lean_object* v___y_2218_ = stack[8].m_obj;
lean_object* v_res_2244_;
v_res_2244_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0(v_type_2210_, v_binds_2211_, v_pre_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
stack->m_obj
 = v_res_2244_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0___boxed(lean_object* v_type_2245_, lean_object* v_binds_2246_, lean_object* v_pre_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0(v_type_2245_, v_binds_2246_, v_pre_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec_ref(v_binds_2246_);
return v_res_2255_;
}
}
lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1(lean_object* v_type_2256_, lean_object* v_pre_2257_, lean_object* v_binds_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v___f_2266_; lean_object* v___x_2267_; 
v___f_2266_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2266_, 0, v_type_2256_);
lean_closure_set(v___f_2266_, 1, v_binds_2258_);
lean_closure_set(v___f_2266_, 2, v_pre_2257_);
v___x_2267_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_2266_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
return v___x_2267_;
}
}
LEAN_EXPORT void l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2256_ = stack[0].m_obj;
lean_object* v_pre_2257_ = stack[1].m_obj;
lean_object* v_binds_2258_ = stack[2].m_obj;
lean_object* v___y_2259_ = stack[3].m_obj;
lean_object* v___y_2260_ = stack[4].m_obj;
lean_object* v___y_2261_ = stack[5].m_obj;
lean_object* v___y_2262_ = stack[6].m_obj;
lean_object* v___y_2263_ = stack[7].m_obj;
lean_object* v___y_2264_ = stack[8].m_obj;
lean_object* v_res_2268_;
v_res_2268_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1(v_type_2256_, v_pre_2257_, v_binds_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
stack->m_obj
 = v_res_2268_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1___boxed(lean_object* v_type_2269_, lean_object* v_pre_2270_, lean_object* v_binds_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1(v_type_2269_, v_pre_2270_, v_binds_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3(lean_object* v_env_2280_, lean_object* v___x_2281_, lean_object* v_currNamespace_2282_, lean_object* v_openDecls_2283_, lean_object* v_n_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2287_ = l_Lean_ResolveName_resolveGlobalName(v_env_2280_, v___x_2281_, v_currNamespace_2282_, v_openDecls_2283_, v_n_2284_);
v___x_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
lean_ctor_set(v___x_2288_, 1, v___y_2286_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3___boxed(lean_object* v_env_2289_, lean_object* v___x_2290_, lean_object* v_currNamespace_2291_, lean_object* v_openDecls_2292_, lean_object* v_n_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3(v_env_2289_, v___x_2290_, v_currNamespace_2291_, v_openDecls_2292_, v_n_2293_, v___y_2294_, v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec_ref(v___x_2290_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(lean_object* v_x_2297_, lean_object* v___y_2298_){
_start:
{
if (lean_obj_tag(v_x_2297_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2300_; 
v_a_2299_ = lean_ctor_get(v_x_2297_, 0);
lean_inc(v_a_2299_);
v___x_2300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2300_, 0, v_a_2299_);
lean_ctor_set(v___x_2300_, 1, v___y_2298_);
return v___x_2300_;
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2302_; 
v_a_2301_ = lean_ctor_get(v_x_2297_, 0);
lean_inc(v_a_2301_);
v___x_2302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2302_, 0, v_a_2301_);
lean_ctor_set(v___x_2302_, 1, v___y_2298_);
return v___x_2302_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg___boxed(lean_object* v_x_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v_x_2303_, v___y_2304_);
lean_dec_ref(v_x_2303_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1(lean_object* v_env_2306_, lean_object* v_stx_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2306_, v_stx_2307_, v___y_2308_, v___y_2309_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
if (lean_obj_tag(v_a_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2320_; 
v_a_2312_ = lean_ctor_get(v___x_2310_, 1);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2320_ == 0)
{
lean_object* v_unused_2321_; 
v_unused_2321_ = lean_ctor_get(v___x_2310_, 0);
lean_dec(v_unused_2321_);
v___x_2314_ = v___x_2310_;
v_isShared_2315_ = v_isSharedCheck_2320_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2310_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2320_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2316_; lean_object* v___x_2318_; 
v___x_2316_ = lean_box(0);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 0, v___x_2316_);
v___x_2318_ = v___x_2314_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_a_2312_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
else
{
lean_object* v_val_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2350_; 
v_val_2322_ = lean_ctor_get(v_a_2311_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v_a_2311_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2324_ = v_a_2311_;
v_isShared_2325_ = v_isSharedCheck_2350_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_val_2322_);
lean_dec(v_a_2311_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2350_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v_snd_2326_; 
v_snd_2326_ = lean_ctor_get(v_val_2322_, 1);
lean_inc(v_snd_2326_);
lean_dec(v_val_2322_);
if (lean_obj_tag(v_snd_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2336_; 
lean_del_object(v___x_2324_);
v_a_2327_ = lean_ctor_get(v___x_2310_, 1);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2310_, 2);
v_a_2328_ = lean_ctor_get(v_snd_2326_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_snd_2326_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2330_ = v_snd_2326_;
v_isShared_2331_ = v_isSharedCheck_2336_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v_snd_2326_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2336_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v___x_2333_, v_a_2327_);
lean_dec_ref(v___x_2333_);
return v___x_2334_;
}
}
}
else
{
lean_object* v_a_2337_; lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2349_; 
v_a_2337_ = lean_ctor_get(v___x_2310_, 1);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2310_, 2);
v_a_2338_ = lean_ctor_get(v_snd_2326_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_snd_2326_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2340_ = v_snd_2326_;
v_isShared_2341_ = v_isSharedCheck_2349_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v_snd_2326_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2349_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v_a_2338_);
v___x_2343_ = v___x_2324_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
lean_object* v___x_2345_; 
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 0, v___x_2343_);
v___x_2345_ = v___x_2340_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2343_);
v___x_2345_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v___x_2345_, v_a_2337_);
lean_dec_ref(v___x_2345_);
return v___x_2346_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
v_a_2351_ = lean_ctor_get(v___x_2310_, 0);
v_a_2352_ = lean_ctor_get(v___x_2310_, 1);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2310_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_inc(v_a_2351_);
lean_dec(v___x_2310_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2351_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_a_2352_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1___boxed(lean_object* v_env_2360_, lean_object* v_stx_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1(v_env_2360_, v_stx_2361_, v___y_2362_, v___y_2363_);
lean_dec_ref(v___y_2362_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0(lean_object* v_env_2365_, lean_object* v_declName_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
uint8_t v___x_2369_; lean_object* v_env_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; uint8_t v___x_2373_; 
v___x_2369_ = 0;
v_env_2370_ = l_Lean_Environment_setExporting(v_env_2365_, v___x_2369_);
lean_inc(v_declName_2366_);
v___x_2371_ = l_Lean_mkPrivateName(v_env_2370_, v_declName_2366_);
v___x_2372_ = 1;
lean_inc_ref(v_env_2370_);
v___x_2373_ = l_Lean_Environment_contains(v_env_2370_, v___x_2371_, v___x_2372_);
if (v___x_2373_ == 0)
{
lean_object* v___x_2374_; uint8_t v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2374_ = l_Lean_privateToUserName(v_declName_2366_);
v___x_2375_ = l_Lean_Environment_contains(v_env_2370_, v___x_2374_, v___x_2372_);
v___x_2376_ = lean_box(v___x_2375_);
v___x_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
lean_ctor_set(v___x_2377_, 1, v___y_2368_);
return v___x_2377_;
}
else
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
lean_dec_ref(v_env_2370_);
lean_dec(v_declName_2366_);
v___x_2378_ = lean_box(v___x_2373_);
v___x_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
lean_ctor_set(v___x_2379_, 1, v___y_2368_);
return v___x_2379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0___boxed(lean_object* v_env_2380_, lean_object* v_declName_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0(v_env_2380_, v_declName_2381_, v___y_2382_, v___y_2383_);
lean_dec_ref(v___y_2382_);
return v_res_2384_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17(lean_object* v_opts_2385_, lean_object* v_opt_2386_){
_start:
{
lean_object* v_name_2387_; lean_object* v_defValue_2388_; lean_object* v_map_2389_; lean_object* v___x_2390_; 
v_name_2387_ = lean_ctor_get(v_opt_2386_, 0);
v_defValue_2388_ = lean_ctor_get(v_opt_2386_, 1);
v_map_2389_ = lean_ctor_get(v_opts_2385_, 0);
v___x_2390_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2389_, v_name_2387_);
if (lean_obj_tag(v___x_2390_) == 0)
{
uint8_t v___x_2391_; 
v___x_2391_ = lean_unbox(v_defValue_2388_);
return v___x_2391_;
}
else
{
lean_object* v_val_2392_; 
v_val_2392_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_val_2392_);
lean_dec_ref_known(v___x_2390_, 1);
if (lean_obj_tag(v_val_2392_) == 1)
{
uint8_t v_v_2393_; 
v_v_2393_ = lean_ctor_get_uint8(v_val_2392_, 0);
lean_dec_ref_known(v_val_2392_, 0);
return v_v_2393_;
}
else
{
uint8_t v___x_2394_; 
lean_dec(v_val_2392_);
v___x_2394_ = lean_unbox(v_defValue_2388_);
return v___x_2394_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_2385_ = stack[0].m_obj;
lean_object* v_opt_2386_ = stack[1].m_obj;
uint8_t v_res_2395_;
v_res_2395_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17(v_opts_2385_, v_opt_2386_);
stack->m_num = v_res_2395_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17___boxed(lean_object* v_opts_2396_, lean_object* v_opt_2397_){
_start:
{
uint8_t v_res_2398_; lean_object* v_r_2399_; 
v_res_2398_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17(v_opts_2396_, v_opt_2397_);
lean_dec_ref(v_opt_2397_);
lean_dec_ref(v_opts_2396_);
v_r_2399_ = lean_box(v_res_2398_);
return v_r_2399_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0(void){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2400_ = lean_box(1);
v___x_2401_ = l_Lean_MessageData_ofFormat(v___x_2400_);
return v___x_2401_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3(void){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__2));
v___x_2406_ = l_Lean_MessageData_ofFormat(v___x_2405_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18(lean_object* v_x_2407_, lean_object* v_x_2408_){
_start:
{
if (lean_obj_tag(v_x_2408_) == 0)
{
return v_x_2407_;
}
else
{
lean_object* v_head_2409_; lean_object* v_tail_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2432_; 
v_head_2409_ = lean_ctor_get(v_x_2408_, 0);
v_tail_2410_ = lean_ctor_get(v_x_2408_, 1);
v_isSharedCheck_2432_ = !lean_is_exclusive(v_x_2408_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2412_ = v_x_2408_;
v_isShared_2413_ = v_isSharedCheck_2432_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_tail_2410_);
lean_inc(v_head_2409_);
lean_dec(v_x_2408_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2432_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v_before_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2430_; 
v_before_2414_ = lean_ctor_get(v_head_2409_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v_head_2409_);
if (v_isSharedCheck_2430_ == 0)
{
lean_object* v_unused_2431_; 
v_unused_2431_ = lean_ctor_get(v_head_2409_, 1);
lean_dec(v_unused_2431_);
v___x_2416_ = v_head_2409_;
v_isShared_2417_ = v_isSharedCheck_2430_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_before_2414_);
lean_dec(v_head_2409_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2430_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2418_; lean_object* v___x_2420_; 
v___x_2418_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0);
if (v_isShared_2417_ == 0)
{
lean_ctor_set_tag(v___x_2416_, 7);
lean_ctor_set(v___x_2416_, 1, v___x_2418_);
lean_ctor_set(v___x_2416_, 0, v_x_2407_);
v___x_2420_ = v___x_2416_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_x_2407_);
lean_ctor_set(v_reuseFailAlloc_2429_, 1, v___x_2418_);
v___x_2420_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
lean_object* v___x_2421_; lean_object* v___x_2423_; 
v___x_2421_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3);
if (v_isShared_2413_ == 0)
{
lean_ctor_set_tag(v___x_2412_, 7);
lean_ctor_set(v___x_2412_, 1, v___x_2421_);
lean_ctor_set(v___x_2412_, 0, v___x_2420_);
v___x_2423_ = v___x_2412_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2420_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v___x_2421_);
v___x_2423_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2424_ = l_Lean_MessageData_ofSyntax(v_before_2414_);
v___x_2425_ = l_Lean_indentD(v___x_2424_);
v___x_2426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2423_);
lean_ctor_set(v___x_2426_, 1, v___x_2425_);
v_x_2407_ = v___x_2426_;
v_x_2408_ = v_tail_2410_;
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
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__1));
v___x_2437_ = l_Lean_MessageData_ofFormat(v___x_2436_);
return v___x_2437_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(lean_object* v_msgData_2438_, lean_object* v_macroStack_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; uint8_t v___x_2444_; 
v___x_2442_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2440_);
v___x_2443_ = l_Lean_Elab_pp_macroStack;
v___x_2444_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17(v___x_2442_, v___x_2443_);
lean_dec_ref(v___x_2442_);
if (v___x_2444_ == 0)
{
lean_object* v___x_2445_; 
lean_dec(v_macroStack_2439_);
v___x_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2445_, 0, v_msgData_2438_);
return v___x_2445_;
}
else
{
if (lean_obj_tag(v_macroStack_2439_) == 0)
{
lean_object* v___x_2446_; 
v___x_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2446_, 0, v_msgData_2438_);
return v___x_2446_;
}
else
{
lean_object* v_head_2447_; lean_object* v_after_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2463_; 
v_head_2447_ = lean_ctor_get(v_macroStack_2439_, 0);
lean_inc(v_head_2447_);
v_after_2448_ = lean_ctor_get(v_head_2447_, 1);
v_isSharedCheck_2463_ = !lean_is_exclusive(v_head_2447_);
if (v_isSharedCheck_2463_ == 0)
{
lean_object* v_unused_2464_; 
v_unused_2464_ = lean_ctor_get(v_head_2447_, 0);
lean_dec(v_unused_2464_);
v___x_2450_ = v_head_2447_;
v_isShared_2451_ = v_isSharedCheck_2463_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_after_2448_);
lean_dec(v_head_2447_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2463_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2452_; lean_object* v___x_2454_; 
v___x_2452_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0);
if (v_isShared_2451_ == 0)
{
lean_ctor_set_tag(v___x_2450_, 7);
lean_ctor_set(v___x_2450_, 1, v___x_2452_);
lean_ctor_set(v___x_2450_, 0, v_msgData_2438_);
v___x_2454_ = v___x_2450_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_msgData_2438_);
lean_ctor_set(v_reuseFailAlloc_2462_, 1, v___x_2452_);
v___x_2454_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v_msgData_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2455_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2);
v___x_2456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2454_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = l_Lean_MessageData_ofSyntax(v_after_2448_);
v___x_2458_ = l_Lean_indentD(v___x_2457_);
v_msgData_2459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2459_, 0, v___x_2456_);
lean_ctor_set(v_msgData_2459_, 1, v___x_2458_);
v___x_2460_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18(v_msgData_2459_, v_macroStack_2439_);
v___x_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2460_);
return v___x_2461_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2438_ = stack[0].m_obj;
lean_object* v_macroStack_2439_ = stack[1].m_obj;
lean_object* v___y_2440_ = stack[2].m_obj;
lean_object* v_res_2465_;
v_res_2465_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_msgData_2438_, v_macroStack_2439_, v___y_2440_);
stack->m_obj
 = v_res_2465_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___boxed(lean_object* v_msgData_2466_, lean_object* v_macroStack_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_msgData_2466_, v_macroStack_2467_, v___y_2468_);
lean_dec_ref(v___y_2468_);
return v_res_2470_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(lean_object* v_msg_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v_ref_2479_; lean_object* v_macroStack_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v_a_2483_; lean_object* v___x_2484_; lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2493_; 
v_ref_2479_ = lean_ctor_get(v___y_2476_, 2);
v_macroStack_2480_ = lean_ctor_get(v___y_2472_, 1);
v___x_2481_ = l_Lean_Elab_getBetterRef(v_ref_2479_, v_macroStack_2480_);
v___x_2482_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msg_2471_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_a_2483_);
lean_dec_ref(v___x_2482_);
lean_inc(v_macroStack_2480_);
v___x_2484_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_a_2483_, v_macroStack_2480_, v___y_2476_);
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2487_ = v___x_2484_;
v_isShared_2488_ = v_isSharedCheck_2493_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2484_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2493_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2489_; lean_object* v___x_2491_; 
v___x_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2481_);
lean_ctor_set(v___x_2489_, 1, v_a_2485_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set_tag(v___x_2487_, 1);
lean_ctor_set(v___x_2487_, 0, v___x_2489_);
v___x_2491_ = v___x_2487_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2489_);
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
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2471_ = stack[0].m_obj;
lean_object* v___y_2472_ = stack[1].m_obj;
lean_object* v___y_2473_ = stack[2].m_obj;
lean_object* v___y_2474_ = stack[3].m_obj;
lean_object* v___y_2475_ = stack[4].m_obj;
lean_object* v___y_2476_ = stack[5].m_obj;
lean_object* v___y_2477_ = stack[6].m_obj;
lean_object* v_res_2494_;
v_res_2494_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
stack->m_obj
 = v_res_2494_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg___boxed(lean_object* v_msg_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
return v_res_2503_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(lean_object* v_ref_2504_, lean_object* v_msg_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v_toCold_2513_; lean_object* v_currRecDepth_2514_; lean_object* v_ref_2515_; uint16_t v_optionFlags_2516_; uint8_t v_suppressElabErrors_2517_; uint8_t v_isRecordingDeps_2518_; lean_object* v_ref_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v_toCold_2513_ = lean_ctor_get(v___y_2510_, 0);
v_currRecDepth_2514_ = lean_ctor_get(v___y_2510_, 1);
v_ref_2515_ = lean_ctor_get(v___y_2510_, 2);
v_optionFlags_2516_ = lean_ctor_get_uint16(v___y_2510_, sizeof(void*)*3);
v_suppressElabErrors_2517_ = lean_ctor_get_uint8(v___y_2510_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2518_ = lean_ctor_get_uint8(v___y_2510_, sizeof(void*)*3 + 3);
v_ref_2519_ = l_Lean_replaceRef(v_ref_2504_, v_ref_2515_);
lean_inc(v_currRecDepth_2514_);
lean_inc_ref(v_toCold_2513_);
v___x_2520_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2520_, 0, v_toCold_2513_);
lean_ctor_set(v___x_2520_, 1, v_currRecDepth_2514_);
lean_ctor_set(v___x_2520_, 2, v_ref_2519_);
lean_ctor_set_uint16(v___x_2520_, sizeof(void*)*3, v_optionFlags_2516_);
lean_ctor_set_uint8(v___x_2520_, sizeof(void*)*3 + 2, v_suppressElabErrors_2517_);
lean_ctor_set_uint8(v___x_2520_, sizeof(void*)*3 + 3, v_isRecordingDeps_2518_);
v___x_2521_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___x_2520_, v___y_2511_);
lean_dec_ref_known(v___x_2520_, 3);
return v___x_2521_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2504_ = stack[0].m_obj;
lean_object* v_msg_2505_ = stack[1].m_obj;
lean_object* v___y_2506_ = stack[2].m_obj;
lean_object* v___y_2507_ = stack[3].m_obj;
lean_object* v___y_2508_ = stack[4].m_obj;
lean_object* v___y_2509_ = stack[5].m_obj;
lean_object* v___y_2510_ = stack[6].m_obj;
lean_object* v___y_2511_ = stack[7].m_obj;
lean_object* v_res_2522_;
v_res_2522_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_ref_2504_, v_msg_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
stack->m_obj
 = v_res_2522_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg___boxed(lean_object* v_ref_2523_, lean_object* v_msg_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_ref_2523_, v_msg_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v_ref_2523_);
return v_res_2532_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2533_; double v___x_2534_; 
v___x_2533_ = lean_unsigned_to_nat(0u);
v___x_2534_ = lean_float_of_nat(v___x_2533_);
return v___x_2534_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(lean_object* v_cls_2537_, lean_object* v_msg_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v_ref_2544_; lean_object* v___x_2545_; lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2591_; 
v_ref_2544_ = lean_ctor_get(v___y_2541_, 2);
v___x_2545_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msg_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2591_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2545_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2591_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2550_; lean_object* v_traceState_2551_; lean_object* v_env_2552_; lean_object* v_nextMacroScope_2553_; lean_object* v_ngen_2554_; lean_object* v_auxDeclNGen_2555_; lean_object* v_cache_2556_; lean_object* v_recordedDeps_2557_; lean_object* v_messages_2558_; lean_object* v_infoState_2559_; lean_object* v_snapshotTasks_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2590_; 
v___x_2550_ = lean_st_ref_take(v___y_2542_);
v_traceState_2551_ = lean_ctor_get(v___x_2550_, 4);
v_env_2552_ = lean_ctor_get(v___x_2550_, 0);
v_nextMacroScope_2553_ = lean_ctor_get(v___x_2550_, 1);
v_ngen_2554_ = lean_ctor_get(v___x_2550_, 2);
v_auxDeclNGen_2555_ = lean_ctor_get(v___x_2550_, 3);
v_cache_2556_ = lean_ctor_get(v___x_2550_, 5);
v_recordedDeps_2557_ = lean_ctor_get(v___x_2550_, 6);
v_messages_2558_ = lean_ctor_get(v___x_2550_, 7);
v_infoState_2559_ = lean_ctor_get(v___x_2550_, 8);
v_snapshotTasks_2560_ = lean_ctor_get(v___x_2550_, 9);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2562_ = v___x_2550_;
v_isShared_2563_ = v_isSharedCheck_2590_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_snapshotTasks_2560_);
lean_inc(v_infoState_2559_);
lean_inc(v_messages_2558_);
lean_inc(v_recordedDeps_2557_);
lean_inc(v_cache_2556_);
lean_inc(v_traceState_2551_);
lean_inc(v_auxDeclNGen_2555_);
lean_inc(v_ngen_2554_);
lean_inc(v_nextMacroScope_2553_);
lean_inc(v_env_2552_);
lean_dec(v___x_2550_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2590_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
uint64_t v_tid_2564_; lean_object* v_traces_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2589_; 
v_tid_2564_ = lean_ctor_get_uint64(v_traceState_2551_, sizeof(void*)*1);
v_traces_2565_ = lean_ctor_get(v_traceState_2551_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v_traceState_2551_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2567_ = v_traceState_2551_;
v_isShared_2568_ = v_isSharedCheck_2589_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_traces_2565_);
lean_dec(v_traceState_2551_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2589_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; double v___x_2571_; uint8_t v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2580_; 
v___x_2569_ = lean_box(0);
v___x_2570_ = lean_box(0);
v___x_2571_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0);
v___x_2572_ = 0;
v___x_2573_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_2574_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2574_, 0, v_cls_2537_);
lean_ctor_set(v___x_2574_, 1, v___x_2570_);
lean_ctor_set(v___x_2574_, 2, v___x_2573_);
lean_ctor_set_float(v___x_2574_, sizeof(void*)*3, v___x_2571_);
lean_ctor_set_float(v___x_2574_, sizeof(void*)*3 + 8, v___x_2571_);
lean_ctor_set_uint8(v___x_2574_, sizeof(void*)*3 + 16, v___x_2572_);
v___x_2575_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__1));
v___x_2576_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2574_);
lean_ctor_set(v___x_2576_, 1, v_a_2546_);
lean_ctor_set(v___x_2576_, 2, v___x_2575_);
lean_inc(v_ref_2544_);
v___x_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2577_, 0, v_ref_2544_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
v___x_2578_ = l_Lean_PersistentArray_push___redArg(v_traces_2565_, v___x_2577_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2578_);
v___x_2580_ = v___x_2567_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2578_);
lean_ctor_set_uint64(v_reuseFailAlloc_2588_, sizeof(void*)*1, v_tid_2564_);
v___x_2580_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
lean_object* v___x_2582_; 
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 4, v___x_2580_);
v___x_2582_ = v___x_2562_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_env_2552_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_nextMacroScope_2553_);
lean_ctor_set(v_reuseFailAlloc_2587_, 2, v_ngen_2554_);
lean_ctor_set(v_reuseFailAlloc_2587_, 3, v_auxDeclNGen_2555_);
lean_ctor_set(v_reuseFailAlloc_2587_, 4, v___x_2580_);
lean_ctor_set(v_reuseFailAlloc_2587_, 5, v_cache_2556_);
lean_ctor_set(v_reuseFailAlloc_2587_, 6, v_recordedDeps_2557_);
lean_ctor_set(v_reuseFailAlloc_2587_, 7, v_messages_2558_);
lean_ctor_set(v_reuseFailAlloc_2587_, 8, v_infoState_2559_);
lean_ctor_set(v_reuseFailAlloc_2587_, 9, v_snapshotTasks_2560_);
v___x_2582_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
lean_object* v___x_2583_; lean_object* v___x_2585_; 
v___x_2583_ = lean_st_ref_put(v___y_2542_, v___x_2582_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v___x_2569_);
v___x_2585_ = v___x_2548_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2569_);
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
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2537_ = stack[0].m_obj;
lean_object* v_msg_2538_ = stack[1].m_obj;
lean_object* v___y_2539_ = stack[2].m_obj;
lean_object* v___y_2540_ = stack[3].m_obj;
lean_object* v___y_2541_ = stack[4].m_obj;
lean_object* v___y_2542_ = stack[5].m_obj;
lean_object* v_res_2592_;
v_res_2592_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_2537_, v_msg_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
stack->m_obj
 = v_res_2592_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___boxed(lean_object* v_cls_2593_, lean_object* v_msg_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_2593_, v_msg_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
return v_res_2600_;
}
}
lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(lean_object* v_as_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
if (lean_obj_tag(v_as_2604_) == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = lean_box(0);
v___x_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
return v___x_2613_;
}
else
{
lean_object* v_toCold_2614_; lean_object* v_options_2615_; uint8_t v_hasTrace_2616_; 
v_toCold_2614_ = lean_ctor_get(v___y_2609_, 0);
v_options_2615_ = lean_ctor_get(v_toCold_2614_, 2);
v_hasTrace_2616_ = lean_ctor_get_uint8(v_options_2615_, sizeof(void*)*1);
if (v_hasTrace_2616_ == 0)
{
lean_object* v_tail_2617_; 
v_tail_2617_ = lean_ctor_get(v_as_2604_, 1);
lean_inc(v_tail_2617_);
lean_dec_ref_known(v_as_2604_, 2);
v_as_2604_ = v_tail_2617_;
goto _start;
}
else
{
lean_object* v_head_2619_; lean_object* v_tail_2620_; lean_object* v_fst_2621_; lean_object* v_snd_2622_; lean_object* v_inheritedTraceOptions_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; uint8_t v___x_2626_; 
v_head_2619_ = lean_ctor_get(v_as_2604_, 0);
lean_inc(v_head_2619_);
v_tail_2620_ = lean_ctor_get(v_as_2604_, 1);
lean_inc(v_tail_2620_);
lean_dec_ref_known(v_as_2604_, 2);
v_fst_2621_ = lean_ctor_get(v_head_2619_, 0);
lean_inc_n(v_fst_2621_, 2);
v_snd_2622_ = lean_ctor_get(v_head_2619_, 1);
lean_inc(v_snd_2622_);
lean_dec(v_head_2619_);
v_inheritedTraceOptions_2623_ = lean_ctor_get(v_toCold_2614_, 11);
v___x_2624_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__1));
v___x_2625_ = l_Lean_Name_append(v___x_2624_, v_fst_2621_);
v___x_2626_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2623_, v_options_2615_, v___x_2625_);
lean_dec(v___x_2625_);
if (v___x_2626_ == 0)
{
lean_dec(v_snd_2622_);
lean_dec(v_fst_2621_);
v_as_2604_ = v_tail_2620_;
goto _start;
}
else
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2628_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2628_, 0, v_snd_2622_);
v___x_2629_ = l_Lean_MessageData_ofFormat(v___x_2628_);
v___x_2630_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_fst_2621_, v___x_2629_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_dec_ref_known(v___x_2630_, 1);
v_as_2604_ = v_tail_2620_;
goto _start;
}
else
{
lean_dec(v_tail_2620_);
return v___x_2630_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2604_ = stack[0].m_obj;
lean_object* v___y_2605_ = stack[1].m_obj;
lean_object* v___y_2606_ = stack[2].m_obj;
lean_object* v___y_2607_ = stack[3].m_obj;
lean_object* v___y_2608_ = stack[4].m_obj;
lean_object* v___y_2609_ = stack[5].m_obj;
lean_object* v___y_2610_ = stack[6].m_obj;
lean_object* v_res_2632_;
v_res_2632_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(v_as_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
stack->m_obj
 = v_res_2632_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___boxed(lean_object* v_as_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(v_as_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
return v_res_2641_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(lean_object* v_keys_2642_, lean_object* v_i_2643_, lean_object* v_k_2644_){
_start:
{
lean_object* v___x_2645_; uint8_t v___x_2646_; 
v___x_2645_ = lean_array_get_size(v_keys_2642_);
v___x_2646_ = lean_nat_dec_lt(v_i_2643_, v___x_2645_);
if (v___x_2646_ == 0)
{
lean_dec(v_i_2643_);
return v___x_2646_;
}
else
{
lean_object* v_k_x27_2647_; uint8_t v___x_2648_; 
v_k_x27_2647_ = lean_array_fget_borrowed(v_keys_2642_, v_i_2643_);
v___x_2648_ = l_Lean_instBEqExtraModUse_beq(v_k_2644_, v_k_x27_2647_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2649_ = lean_unsigned_to_nat(1u);
v___x_2650_ = lean_nat_add(v_i_2643_, v___x_2649_);
lean_dec(v_i_2643_);
v_i_2643_ = v___x_2650_;
goto _start;
}
else
{
lean_dec(v_i_2643_);
return v___x_2646_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2642_ = stack[0].m_obj;
lean_object* v_i_2643_ = stack[1].m_obj;
lean_object* v_k_2644_ = stack[2].m_obj;
uint8_t v_res_2652_;
v_res_2652_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_keys_2642_, v_i_2643_, v_k_2644_);
stack->m_num = v_res_2652_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg___boxed(lean_object* v_keys_2653_, lean_object* v_i_2654_, lean_object* v_k_2655_){
_start:
{
uint8_t v_res_2656_; lean_object* v_r_2657_; 
v_res_2656_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_keys_2653_, v_i_2654_, v_k_2655_);
lean_dec_ref(v_k_2655_);
lean_dec_ref(v_keys_2653_);
v_r_2657_ = lean_box(v_res_2656_);
return v_r_2657_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(lean_object* v_x_2658_, size_t v_x_2659_, lean_object* v_x_2660_){
_start:
{
if (lean_obj_tag(v_x_2658_) == 0)
{
lean_object* v_es_2661_; lean_object* v___x_2662_; size_t v___x_2663_; size_t v___x_2664_; lean_object* v_j_2665_; lean_object* v___x_2666_; 
v_es_2661_ = lean_ctor_get(v_x_2658_, 0);
v___x_2662_ = lean_box(2);
v___x_2663_ = ((size_t)31ULL);
v___x_2664_ = lean_usize_land(v_x_2659_, v___x_2663_);
v_j_2665_ = lean_usize_to_nat(v___x_2664_);
v___x_2666_ = lean_array_get_borrowed(v___x_2662_, v_es_2661_, v_j_2665_);
lean_dec(v_j_2665_);
switch(lean_obj_tag(v___x_2666_))
{
case 0:
{
lean_object* v_key_2667_; uint8_t v___x_2668_; 
v_key_2667_ = lean_ctor_get(v___x_2666_, 0);
v___x_2668_ = l_Lean_instBEqExtraModUse_beq(v_x_2660_, v_key_2667_);
return v___x_2668_;
}
case 1:
{
lean_object* v_node_2669_; size_t v___x_2670_; size_t v___x_2671_; 
v_node_2669_ = lean_ctor_get(v___x_2666_, 0);
v___x_2670_ = ((size_t)5ULL);
v___x_2671_ = lean_usize_shift_right(v_x_2659_, v___x_2670_);
v_x_2658_ = v_node_2669_;
v_x_2659_ = v___x_2671_;
goto _start;
}
default: 
{
uint8_t v___x_2673_; 
v___x_2673_ = 0;
return v___x_2673_;
}
}
}
else
{
lean_object* v_ks_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
v_ks_2674_ = lean_ctor_get(v_x_2658_, 0);
v___x_2675_ = lean_unsigned_to_nat(0u);
v___x_2676_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_ks_2674_, v___x_2675_, v_x_2660_);
return v___x_2676_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2658_ = stack[0].m_obj;
size_t v_x_2659_ = stack[1].m_num;
lean_object* v_x_2660_ = stack[2].m_obj;
uint8_t v_res_2677_;
v_res_2677_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_2658_, v_x_2659_, v_x_2660_);
stack->m_num = v_res_2677_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_x_2678_, lean_object* v_x_2679_, lean_object* v_x_2680_){
_start:
{
size_t v_x_15250__boxed_2681_; uint8_t v_res_2682_; lean_object* v_r_2683_; 
v_x_15250__boxed_2681_ = lean_unbox_usize(v_x_2679_);
lean_dec(v_x_2679_);
v_res_2682_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_2678_, v_x_15250__boxed_2681_, v_x_2680_);
lean_dec_ref(v_x_2680_);
lean_dec_ref(v_x_2678_);
v_r_2683_ = lean_box(v_res_2682_);
return v_r_2683_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(lean_object* v_x_2684_, lean_object* v_x_2685_){
_start:
{
uint64_t v___x_2686_; size_t v___x_2687_; uint8_t v___x_2688_; 
v___x_2686_ = l_Lean_instHashableExtraModUse_hash(v_x_2685_);
v___x_2687_ = lean_uint64_to_usize(v___x_2686_);
v___x_2688_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_2684_, v___x_2687_, v_x_2685_);
return v___x_2688_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2684_ = stack[0].m_obj;
lean_object* v_x_2685_ = stack[1].m_obj;
uint8_t v_res_2689_;
v_res_2689_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v_x_2684_, v_x_2685_);
stack->m_num = v_res_2689_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_x_2690_, lean_object* v_x_2691_){
_start:
{
uint8_t v_res_2692_; lean_object* v_r_2693_; 
v_res_2692_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v_x_2690_, v_x_2691_);
lean_dec_ref(v_x_2691_);
lean_dec_ref(v_x_2690_);
v_r_2693_ = lean_box(v_res_2692_);
return v_r_2693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___lam__0(lean_object* v___x_2694_, lean_object* v_entry_2695_, lean_object* v_s_2696_){
_start:
{
lean_object* v_addEntryFn_2697_; lean_object* v_importedEntries_2698_; lean_object* v_state_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2707_; 
v_addEntryFn_2697_ = lean_ctor_get(v___x_2694_, 3);
lean_inc(v_addEntryFn_2697_);
lean_dec_ref(v___x_2694_);
v_importedEntries_2698_ = lean_ctor_get(v_s_2696_, 0);
v_state_2699_ = lean_ctor_get(v_s_2696_, 1);
v_isSharedCheck_2707_ = !lean_is_exclusive(v_s_2696_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2701_ = v_s_2696_;
v_isShared_2702_ = v_isSharedCheck_2707_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_state_2699_);
lean_inc(v_importedEntries_2698_);
lean_dec(v_s_2696_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2707_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v_state_2703_; lean_object* v___x_2705_; 
v_state_2703_ = lean_apply_2(v_addEntryFn_2697_, v_state_2699_, v_entry_2695_);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 1, v_state_2703_);
v___x_2705_ = v___x_2701_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_importedEntries_2698_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v_state_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2708_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
return v___x_2709_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2710_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0);
v___x_2711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
return v___x_2711_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2712_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0);
v___x_2713_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
lean_ctor_set(v___x_2713_, 2, v___x_2712_);
lean_ctor_set(v___x_2713_, 3, v___x_2712_);
lean_ctor_set(v___x_2713_, 4, v___x_2712_);
lean_ctor_set(v___x_2713_, 5, v___x_2712_);
return v___x_2713_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2714_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7(void){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2719_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6));
v___x_2720_ = l_Lean_stringToMessageData(v___x_2719_);
return v___x_2720_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9(void){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__8));
v___x_2723_ = l_Lean_stringToMessageData(v___x_2722_);
return v___x_2723_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10(void){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_2725_ = l_Lean_stringToMessageData(v___x_2724_);
return v___x_2725_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11(void){
_start:
{
lean_object* v_cls_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v_cls_2726_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5));
v___x_2727_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__1));
v___x_2728_ = l_Lean_Name_append(v___x_2727_, v_cls_2726_);
return v___x_2728_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13(void){
_start:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2730_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12));
v___x_2731_ = l_Lean_stringToMessageData(v___x_2730_);
return v___x_2731_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15(void){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14));
v___x_2734_ = l_Lean_stringToMessageData(v___x_2733_);
return v___x_2734_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(lean_object* v_mod_2739_, uint8_t v_isMeta_2740_, lean_object* v_hint_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v_env_2783_; uint8_t v_isExporting_2784_; lean_object* v_entry_2785_; lean_object* v___x_2786_; lean_object* v_env_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; uint8_t v___x_2792_; 
v___x_2781_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3);
v___x_2782_ = lean_st_ref_get(v___y_2747_);
v_env_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc_ref(v_env_2783_);
lean_dec(v___x_2782_);
v_isExporting_2784_ = lean_ctor_get_uint8(v_env_2783_, sizeof(void*)*13);
lean_dec_ref(v_env_2783_);
lean_inc(v_mod_2739_);
v_entry_2785_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2785_, 0, v_mod_2739_);
lean_ctor_set_uint8(v_entry_2785_, sizeof(void*)*1, v_isExporting_2784_);
lean_ctor_set_uint8(v_entry_2785_, sizeof(void*)*1 + 1, v_isMeta_2740_);
v___x_2786_ = lean_st_ref_get(v___y_2747_);
v_env_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc_ref(v_env_2787_);
lean_dec(v___x_2786_);
v___x_2788_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2789_ = lean_box(1);
v___x_2790_ = lean_box(0);
v___x_2791_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2781_, v___x_2788_, v_env_2787_, v___x_2789_, v___x_2790_);
v___x_2792_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v___x_2791_, v_entry_2785_);
lean_dec(v___x_2791_);
if (v___x_2792_ == 0)
{
lean_object* v_toCold_2793_; lean_object* v_options_2794_; lean_object* v_inheritedTraceOptions_2795_; uint8_t v_hasTrace_2796_; lean_object* v___f_2797_; uint8_t v___x_2798_; lean_object* v___y_2800_; lean_object* v___y_2801_; 
v_toCold_2793_ = lean_ctor_get(v___y_2746_, 0);
v_options_2794_ = lean_ctor_get(v_toCold_2793_, 2);
v_inheritedTraceOptions_2795_ = lean_ctor_get(v_toCold_2793_, 11);
v_hasTrace_2796_ = lean_ctor_get_uint8(v_options_2794_, sizeof(void*)*1);
v___f_2797_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___lam__0), 3, 2);
lean_closure_set(v___f_2797_, 0, v___x_2788_);
lean_closure_set(v___f_2797_, 1, v_entry_2785_);
v___x_2798_ = 1;
if (v_hasTrace_2796_ == 0)
{
lean_dec(v_hint_2741_);
lean_dec(v_mod_2739_);
v___y_2800_ = v___y_2745_;
v___y_2801_ = v___y_2747_;
goto v___jp_2799_;
}
else
{
lean_object* v_cls_2828_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___x_2848_; uint8_t v___x_2849_; 
v_cls_2828_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5));
v___x_2848_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11);
v___x_2849_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2795_, v_options_2794_, v___x_2848_);
if (v___x_2849_ == 0)
{
lean_dec(v_hint_2741_);
lean_dec(v_mod_2739_);
v___y_2800_ = v___y_2745_;
v___y_2801_ = v___y_2747_;
goto v___jp_2799_;
}
else
{
lean_object* v___x_2850_; lean_object* v___y_2852_; 
v___x_2850_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13);
if (v_isExporting_2784_ == 0)
{
lean_object* v___x_2859_; 
v___x_2859_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18));
v___y_2852_ = v___x_2859_;
goto v___jp_2851_;
}
else
{
lean_object* v___x_2860_; 
v___x_2860_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__19));
v___y_2852_ = v___x_2860_;
goto v___jp_2851_;
}
v___jp_2851_:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
lean_inc_ref(v___y_2852_);
v___x_2853_ = l_Lean_stringToMessageData(v___y_2852_);
v___x_2854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2850_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
v___x_2855_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15);
v___x_2856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2854_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
if (v_isMeta_2740_ == 0)
{
lean_object* v___x_2857_; 
v___x_2857_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16));
v___y_2835_ = v___x_2856_;
v___y_2836_ = v___x_2857_;
goto v___jp_2834_;
}
else
{
lean_object* v___x_2858_; 
v___x_2858_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__17));
v___y_2835_ = v___x_2856_;
v___y_2836_ = v___x_2858_;
goto v___jp_2834_;
}
}
}
v___jp_2829_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2832_, 0, v___y_2830_);
lean_ctor_set(v___x_2832_, 1, v___y_2831_);
v___x_2833_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_2828_, v___x_2832_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_dec_ref_known(v___x_2833_, 1);
v___y_2800_ = v___y_2745_;
v___y_2801_ = v___y_2747_;
goto v___jp_2799_;
}
else
{
lean_dec_ref(v___f_2797_);
return v___x_2833_;
}
}
v___jp_2834_:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; uint8_t v___x_2843_; 
lean_inc_ref(v___y_2836_);
v___x_2837_ = l_Lean_stringToMessageData(v___y_2836_);
v___x_2838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___y_2835_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7);
v___x_2840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2838_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
v___x_2841_ = l_Lean_MessageData_ofName(v_mod_2739_);
v___x_2842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2840_);
lean_ctor_set(v___x_2842_, 1, v___x_2841_);
v___x_2843_ = l_Lean_Name_isAnonymous(v_hint_2741_);
if (v___x_2843_ == 0)
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2844_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9);
v___x_2845_ = l_Lean_MessageData_ofName(v_hint_2741_);
v___x_2846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2844_);
lean_ctor_set(v___x_2846_, 1, v___x_2845_);
v___y_2830_ = v___x_2842_;
v___y_2831_ = v___x_2846_;
goto v___jp_2829_;
}
else
{
lean_object* v___x_2847_; 
lean_dec(v_hint_2741_);
v___x_2847_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10);
v___y_2830_ = v___x_2842_;
v___y_2831_ = v___x_2847_;
goto v___jp_2829_;
}
}
}
v___jp_2799_:
{
lean_object* v___x_2802_; lean_object* v_toEnvExtension_2803_; uint8_t v_logWrites_2804_; 
v___x_2802_ = lean_st_ref_take(v___y_2801_);
v_toEnvExtension_2803_ = lean_ctor_get(v___x_2788_, 0);
v_logWrites_2804_ = lean_ctor_get_uint8(v_toEnvExtension_2803_, sizeof(void*)*6);
if (v_logWrites_2804_ == 0)
{
lean_object* v_env_2805_; lean_object* v_nextMacroScope_2806_; lean_object* v_ngen_2807_; lean_object* v_auxDeclNGen_2808_; lean_object* v_traceState_2809_; lean_object* v_recordedDeps_2810_; lean_object* v_messages_2811_; lean_object* v_infoState_2812_; lean_object* v_snapshotTasks_2813_; lean_object* v_asyncMode_2814_; lean_object* v___x_2815_; 
v_env_2805_ = lean_ctor_get(v___x_2802_, 0);
lean_inc_ref(v_env_2805_);
v_nextMacroScope_2806_ = lean_ctor_get(v___x_2802_, 1);
lean_inc(v_nextMacroScope_2806_);
v_ngen_2807_ = lean_ctor_get(v___x_2802_, 2);
lean_inc_ref(v_ngen_2807_);
v_auxDeclNGen_2808_ = lean_ctor_get(v___x_2802_, 3);
lean_inc_ref(v_auxDeclNGen_2808_);
v_traceState_2809_ = lean_ctor_get(v___x_2802_, 4);
lean_inc_ref(v_traceState_2809_);
v_recordedDeps_2810_ = lean_ctor_get(v___x_2802_, 6);
lean_inc_ref(v_recordedDeps_2810_);
v_messages_2811_ = lean_ctor_get(v___x_2802_, 7);
lean_inc_ref(v_messages_2811_);
v_infoState_2812_ = lean_ctor_get(v___x_2802_, 8);
lean_inc_ref(v_infoState_2812_);
v_snapshotTasks_2813_ = lean_ctor_get(v___x_2802_, 9);
lean_inc_ref(v_snapshotTasks_2813_);
lean_dec(v___x_2802_);
v_asyncMode_2814_ = lean_ctor_get(v_toEnvExtension_2803_, 2);
lean_inc_ref(v_toEnvExtension_2803_);
v___x_2815_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2803_, v_env_2805_, v___f_2797_, v_asyncMode_2814_, v___x_2790_, v___x_2798_);
v___y_2750_ = v_recordedDeps_2810_;
v___y_2751_ = v_infoState_2812_;
v___y_2752_ = v_nextMacroScope_2806_;
v___y_2753_ = v___y_2801_;
v___y_2754_ = v___y_2800_;
v___y_2755_ = v_auxDeclNGen_2808_;
v___y_2756_ = v_ngen_2807_;
v___y_2757_ = v_snapshotTasks_2813_;
v___y_2758_ = v_traceState_2809_;
v___y_2759_ = v_messages_2811_;
v___y_2760_ = v___x_2815_;
goto v___jp_2749_;
}
else
{
lean_object* v_env_2816_; lean_object* v_nextMacroScope_2817_; lean_object* v_ngen_2818_; lean_object* v_auxDeclNGen_2819_; lean_object* v_traceState_2820_; lean_object* v_recordedDeps_2821_; lean_object* v_messages_2822_; lean_object* v_infoState_2823_; lean_object* v_snapshotTasks_2824_; lean_object* v_asyncMode_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v_env_2816_ = lean_ctor_get(v___x_2802_, 0);
lean_inc_ref(v_env_2816_);
v_nextMacroScope_2817_ = lean_ctor_get(v___x_2802_, 1);
lean_inc(v_nextMacroScope_2817_);
v_ngen_2818_ = lean_ctor_get(v___x_2802_, 2);
lean_inc_ref(v_ngen_2818_);
v_auxDeclNGen_2819_ = lean_ctor_get(v___x_2802_, 3);
lean_inc_ref(v_auxDeclNGen_2819_);
v_traceState_2820_ = lean_ctor_get(v___x_2802_, 4);
lean_inc_ref(v_traceState_2820_);
v_recordedDeps_2821_ = lean_ctor_get(v___x_2802_, 6);
lean_inc_ref(v_recordedDeps_2821_);
v_messages_2822_ = lean_ctor_get(v___x_2802_, 7);
lean_inc_ref(v_messages_2822_);
v_infoState_2823_ = lean_ctor_get(v___x_2802_, 8);
lean_inc_ref(v_infoState_2823_);
v_snapshotTasks_2824_ = lean_ctor_get(v___x_2802_, 9);
lean_inc_ref(v_snapshotTasks_2824_);
lean_dec(v___x_2802_);
v_asyncMode_2825_ = lean_ctor_get(v_toEnvExtension_2803_, 2);
lean_inc_ref_n(v_toEnvExtension_2803_, 2);
v___x_2826_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2803_, v_env_2816_);
lean_dec_ref(v_env_2816_);
v___x_2827_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2803_, v___x_2826_, v___f_2797_, v_asyncMode_2825_, v___x_2790_, v___x_2798_);
v___y_2750_ = v_recordedDeps_2821_;
v___y_2751_ = v_infoState_2823_;
v___y_2752_ = v_nextMacroScope_2817_;
v___y_2753_ = v___y_2801_;
v___y_2754_ = v___y_2800_;
v___y_2755_ = v_auxDeclNGen_2819_;
v___y_2756_ = v_ngen_2818_;
v___y_2757_ = v_snapshotTasks_2824_;
v___y_2758_ = v_traceState_2820_;
v___y_2759_ = v_messages_2822_;
v___y_2760_ = v___x_2827_;
goto v___jp_2749_;
}
}
}
else
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
lean_dec_ref_known(v_entry_2785_, 1);
lean_dec(v_hint_2741_);
lean_dec(v_mod_2739_);
v___x_2861_ = lean_box(0);
v___x_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
return v___x_2862_;
}
v___jp_2749_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v_mctx_2765_; lean_object* v_zetaDeltaFVarIds_2766_; lean_object* v_postponed_2767_; lean_object* v_diag_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2779_; 
v___x_2761_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1);
v___x_2762_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2762_, 0, v___y_2760_);
lean_ctor_set(v___x_2762_, 1, v___y_2752_);
lean_ctor_set(v___x_2762_, 2, v___y_2756_);
lean_ctor_set(v___x_2762_, 3, v___y_2755_);
lean_ctor_set(v___x_2762_, 4, v___y_2758_);
lean_ctor_set(v___x_2762_, 5, v___x_2761_);
lean_ctor_set(v___x_2762_, 6, v___y_2750_);
lean_ctor_set(v___x_2762_, 7, v___y_2759_);
lean_ctor_set(v___x_2762_, 8, v___y_2751_);
lean_ctor_set(v___x_2762_, 9, v___y_2757_);
v___x_2763_ = lean_st_ref_put(v___y_2753_, v___x_2762_);
v___x_2764_ = lean_st_ref_take(v___y_2754_);
v_mctx_2765_ = lean_ctor_get(v___x_2764_, 0);
v_zetaDeltaFVarIds_2766_ = lean_ctor_get(v___x_2764_, 2);
v_postponed_2767_ = lean_ctor_get(v___x_2764_, 3);
v_diag_2768_ = lean_ctor_get(v___x_2764_, 4);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2779_ == 0)
{
lean_object* v_unused_2780_; 
v_unused_2780_ = lean_ctor_get(v___x_2764_, 1);
lean_dec(v_unused_2780_);
v___x_2770_ = v___x_2764_;
v_isShared_2771_ = v_isSharedCheck_2779_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_diag_2768_);
lean_inc(v_postponed_2767_);
lean_inc(v_zetaDeltaFVarIds_2766_);
lean_inc(v_mctx_2765_);
lean_dec(v___x_2764_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2779_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2775_; 
v___x_2772_ = lean_box(0);
v___x_2773_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2);
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 1, v___x_2773_);
v___x_2775_ = v___x_2770_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_mctx_2765_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v___x_2773_);
lean_ctor_set(v_reuseFailAlloc_2778_, 2, v_zetaDeltaFVarIds_2766_);
lean_ctor_set(v_reuseFailAlloc_2778_, 3, v_postponed_2767_);
lean_ctor_set(v_reuseFailAlloc_2778_, 4, v_diag_2768_);
v___x_2775_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2776_ = lean_st_ref_put(v___y_2754_, v___x_2775_);
v___x_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2772_);
return v___x_2777_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_2739_ = stack[0].m_obj;
uint8_t v_isMeta_2740_ = stack[1].m_num;
lean_object* v_hint_2741_ = stack[2].m_obj;
lean_object* v___y_2742_ = stack[3].m_obj;
lean_object* v___y_2743_ = stack[4].m_obj;
lean_object* v___y_2744_ = stack[5].m_obj;
lean_object* v___y_2745_ = stack[6].m_obj;
lean_object* v___y_2746_ = stack[7].m_obj;
lean_object* v___y_2747_ = stack[8].m_obj;
lean_object* v_res_2863_;
v_res_2863_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_mod_2739_, v_isMeta_2740_, v_hint_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
stack->m_obj
 = v_res_2863_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___boxed(lean_object* v_mod_2864_, lean_object* v_isMeta_2865_, lean_object* v_hint_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
uint8_t v_isMeta_boxed_2874_; lean_object* v_res_2875_; 
v_isMeta_boxed_2874_ = lean_unbox(v_isMeta_2865_);
v_res_2875_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_mod_2864_, v_isMeta_boxed_2874_, v_hint_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
return v_res_2875_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(lean_object* v___x_2876_, lean_object* v_declName_2877_, lean_object* v_as_2878_, size_t v_sz_2879_, size_t v_i_2880_, lean_object* v_b_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
uint8_t v___x_2889_; 
v___x_2889_ = lean_usize_dec_lt(v_i_2880_, v_sz_2879_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2890_; 
lean_dec(v_declName_2877_);
v___x_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2890_, 0, v_b_2881_);
return v___x_2890_;
}
else
{
lean_object* v___x_2891_; lean_object* v_modules_2892_; lean_object* v___x_2893_; lean_object* v_a_2894_; lean_object* v___x_2895_; lean_object* v_toImport_2896_; lean_object* v_module_2897_; lean_object* v___x_2898_; uint8_t v___x_2899_; lean_object* v___x_2900_; 
v___x_2891_ = l_Lean_Environment_header(v___x_2876_);
v_modules_2892_ = lean_ctor_get(v___x_2891_, 3);
lean_inc_ref(v_modules_2892_);
lean_dec_ref(v___x_2891_);
v___x_2893_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2894_ = lean_array_uget_borrowed(v_as_2878_, v_i_2880_);
v___x_2895_ = lean_array_get(v___x_2893_, v_modules_2892_, v_a_2894_);
lean_dec_ref(v_modules_2892_);
v_toImport_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc_ref(v_toImport_2896_);
lean_dec(v___x_2895_);
v_module_2897_ = lean_ctor_get(v_toImport_2896_, 0);
lean_inc(v_module_2897_);
lean_dec_ref(v_toImport_2896_);
v___x_2898_ = lean_box(0);
v___x_2899_ = 0;
lean_inc(v_declName_2877_);
v___x_2900_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_module_2897_, v___x_2899_, v_declName_2877_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
if (lean_obj_tag(v___x_2900_) == 0)
{
size_t v___x_2901_; size_t v___x_2902_; 
lean_dec_ref_known(v___x_2900_, 1);
v___x_2901_ = ((size_t)1ULL);
v___x_2902_ = lean_usize_add(v_i_2880_, v___x_2901_);
v_i_2880_ = v___x_2902_;
v_b_2881_ = v___x_2898_;
goto _start;
}
else
{
lean_dec(v_declName_2877_);
return v___x_2900_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2876_ = stack[0].m_obj;
lean_object* v_declName_2877_ = stack[1].m_obj;
lean_object* v_as_2878_ = stack[2].m_obj;
size_t v_sz_2879_ = stack[3].m_num;
size_t v_i_2880_ = stack[4].m_num;
lean_object* v_b_2881_ = stack[5].m_obj;
lean_object* v___y_2882_ = stack[6].m_obj;
lean_object* v___y_2883_ = stack[7].m_obj;
lean_object* v___y_2884_ = stack[8].m_obj;
lean_object* v___y_2885_ = stack[9].m_obj;
lean_object* v___y_2886_ = stack[10].m_obj;
lean_object* v___y_2887_ = stack[11].m_obj;
lean_object* v_res_2904_;
v_res_2904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(v___x_2876_, v_declName_2877_, v_as_2878_, v_sz_2879_, v_i_2880_, v_b_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
stack->m_obj
 = v_res_2904_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5___boxed(lean_object* v___x_2905_, lean_object* v_declName_2906_, lean_object* v_as_2907_, lean_object* v_sz_2908_, lean_object* v_i_2909_, lean_object* v_b_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
size_t v_sz_boxed_2918_; size_t v_i_boxed_2919_; lean_object* v_res_2920_; 
v_sz_boxed_2918_ = lean_unbox_usize(v_sz_2908_);
lean_dec(v_sz_2908_);
v_i_boxed_2919_ = lean_unbox_usize(v_i_2909_);
lean_dec(v_i_2909_);
v_res_2920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(v___x_2905_, v_declName_2906_, v_as_2907_, v_sz_boxed_2918_, v_i_boxed_2919_, v_b_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec_ref(v_as_2907_);
lean_dec_ref(v___x_2905_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(lean_object* v_a_2921_, lean_object* v_x_2922_){
_start:
{
if (lean_obj_tag(v_x_2922_) == 0)
{
lean_object* v___x_2923_; 
v___x_2923_ = lean_box(0);
return v___x_2923_;
}
else
{
lean_object* v_key_2924_; lean_object* v_value_2925_; lean_object* v_tail_2926_; uint8_t v___x_2927_; 
v_key_2924_ = lean_ctor_get(v_x_2922_, 0);
v_value_2925_ = lean_ctor_get(v_x_2922_, 1);
v_tail_2926_ = lean_ctor_get(v_x_2922_, 2);
v___x_2927_ = lean_name_eq(v_key_2924_, v_a_2921_);
if (v___x_2927_ == 0)
{
v_x_2922_ = v_tail_2926_;
goto _start;
}
else
{
lean_object* v___x_2929_; 
lean_inc(v_value_2925_);
v___x_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2929_, 0, v_value_2925_);
return v___x_2929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_a_2930_, lean_object* v_x_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(v_a_2930_, v_x_2931_);
lean_dec(v_x_2931_);
lean_dec(v_a_2930_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(lean_object* v_m_2933_, lean_object* v_a_2934_){
_start:
{
lean_object* v_buckets_2935_; lean_object* v___x_2936_; uint64_t v___y_2938_; 
v_buckets_2935_ = lean_ctor_get(v_m_2933_, 1);
v___x_2936_ = lean_array_get_size(v_buckets_2935_);
if (lean_obj_tag(v_a_2934_) == 0)
{
uint64_t v___x_2952_; 
v___x_2952_ = 1723ULL;
v___y_2938_ = v___x_2952_;
goto v___jp_2937_;
}
else
{
uint64_t v_hash_2953_; 
v_hash_2953_ = lean_ctor_get_uint64(v_a_2934_, sizeof(void*)*2);
v___y_2938_ = v_hash_2953_;
goto v___jp_2937_;
}
v___jp_2937_:
{
uint64_t v___x_2939_; uint64_t v___x_2940_; uint64_t v_fold_2941_; uint64_t v___x_2942_; uint64_t v___x_2943_; uint64_t v___x_2944_; size_t v___x_2945_; size_t v___x_2946_; size_t v___x_2947_; size_t v___x_2948_; size_t v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2939_ = 32ULL;
v___x_2940_ = lean_uint64_shift_right(v___y_2938_, v___x_2939_);
v_fold_2941_ = lean_uint64_xor(v___y_2938_, v___x_2940_);
v___x_2942_ = 16ULL;
v___x_2943_ = lean_uint64_shift_right(v_fold_2941_, v___x_2942_);
v___x_2944_ = lean_uint64_xor(v_fold_2941_, v___x_2943_);
v___x_2945_ = lean_uint64_to_usize(v___x_2944_);
v___x_2946_ = lean_usize_of_nat(v___x_2936_);
v___x_2947_ = ((size_t)1ULL);
v___x_2948_ = lean_usize_sub(v___x_2946_, v___x_2947_);
v___x_2949_ = lean_usize_land(v___x_2945_, v___x_2948_);
v___x_2950_ = lean_array_uget_borrowed(v_buckets_2935_, v___x_2949_);
v___x_2951_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(v_a_2934_, v___x_2950_);
return v___x_2951_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_m_2954_, lean_object* v_a_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(v_m_2954_, v_a_2955_);
lean_dec(v_a_2955_);
lean_dec_ref(v_m_2954_);
return v_res_2956_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2957_;
}
}
lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(lean_object* v_declName_2960_, uint8_t v_isMeta_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v_env_2974_; lean_object* v___y_2976_; lean_object* v___x_2989_; 
v___x_2969_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0);
v___x_2970_ = lean_st_ref_get(v___y_2967_);
v_env_2974_ = lean_ctor_get(v___x_2970_, 0);
lean_inc_ref(v_env_2974_);
lean_dec(v___x_2970_);
v___x_2989_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2974_, v_declName_2960_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_dec_ref(v_env_2974_);
lean_dec(v_declName_2960_);
goto v___jp_2971_;
}
else
{
lean_object* v_val_2990_; lean_object* v___x_2991_; lean_object* v_modules_2992_; lean_object* v___x_2993_; uint8_t v___x_2994_; 
v_val_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_val_2990_);
lean_dec_ref_known(v___x_2989_, 1);
v___x_2991_ = l_Lean_Environment_header(v_env_2974_);
v_modules_2992_ = lean_ctor_get(v___x_2991_, 3);
lean_inc_ref(v_modules_2992_);
lean_dec_ref(v___x_2991_);
v___x_2993_ = lean_array_get_size(v_modules_2992_);
v___x_2994_ = lean_nat_dec_lt(v_val_2990_, v___x_2993_);
if (v___x_2994_ == 0)
{
lean_dec_ref(v_modules_2992_);
lean_dec(v_val_2990_);
lean_dec_ref(v_env_2974_);
lean_dec(v_declName_2960_);
goto v___jp_2971_;
}
else
{
lean_object* v___x_2995_; lean_object* v___x_2996_; uint8_t v___y_2998_; 
v___x_2995_ = lean_array_fget(v_modules_2992_, v_val_2990_);
lean_dec(v_val_2990_);
lean_dec_ref(v_modules_2992_);
v___x_2996_ = lean_st_ref_get(v___y_2967_);
if (v_isMeta_2961_ == 0)
{
lean_dec(v___x_2996_);
v___y_2998_ = v_isMeta_2961_;
goto v___jp_2997_;
}
else
{
lean_object* v_env_3009_; uint8_t v___x_3010_; 
v_env_3009_ = lean_ctor_get(v___x_2996_, 0);
lean_inc_ref(v_env_3009_);
lean_dec(v___x_2996_);
lean_inc(v_declName_2960_);
v___x_3010_ = l_Lean_isMarkedMeta(v_env_3009_, v_declName_2960_);
if (v___x_3010_ == 0)
{
v___y_2998_ = v_isMeta_2961_;
goto v___jp_2997_;
}
else
{
uint8_t v___x_3011_; 
v___x_3011_ = 0;
v___y_2998_ = v___x_3011_;
goto v___jp_2997_;
}
}
v___jp_2997_:
{
lean_object* v_toImport_2999_; lean_object* v_module_3000_; lean_object* v___x_3001_; 
v_toImport_2999_ = lean_ctor_get(v___x_2995_, 0);
lean_inc_ref(v_toImport_2999_);
lean_dec(v___x_2995_);
v_module_3000_ = lean_ctor_get(v_toImport_2999_, 0);
lean_inc(v_module_3000_);
lean_dec_ref(v_toImport_2999_);
lean_inc(v_declName_2960_);
v___x_3001_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_module_3000_, v___y_2998_, v_declName_2960_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
lean_dec_ref_known(v___x_3001_, 1);
v___x_3002_ = l_Lean_indirectModUseExt;
v___x_3003_ = lean_box(1);
v___x_3004_ = lean_box(0);
lean_inc_ref(v_env_2974_);
v___x_3005_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2969_, v___x_3002_, v_env_2974_, v___x_3003_, v___x_3004_);
v___x_3006_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(v___x_3005_, v_declName_2960_);
lean_dec(v___x_3005_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v___x_3007_; 
v___x_3007_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__1));
v___y_2976_ = v___x_3007_;
goto v___jp_2975_;
}
else
{
lean_object* v_val_3008_; 
v_val_3008_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_val_3008_);
lean_dec_ref_known(v___x_3006_, 1);
v___y_2976_ = v_val_3008_;
goto v___jp_2975_;
}
}
else
{
lean_dec_ref(v_env_2974_);
lean_dec(v_declName_2960_);
return v___x_3001_;
}
}
}
}
v___jp_2971_:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2972_ = lean_box(0);
v___x_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
return v___x_2973_;
}
v___jp_2975_:
{
lean_object* v___x_2977_; size_t v_sz_2978_; size_t v___x_2979_; lean_object* v___x_2980_; 
v___x_2977_ = lean_box(0);
v_sz_2978_ = lean_array_size(v___y_2976_);
v___x_2979_ = ((size_t)0ULL);
v___x_2980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(v_env_2974_, v_declName_2960_, v___y_2976_, v_sz_2978_, v___x_2979_, v___x_2977_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
lean_dec_ref(v___y_2976_);
lean_dec_ref(v_env_2974_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; 
v_unused_2988_ = lean_ctor_get(v___x_2980_, 0);
lean_dec(v_unused_2988_);
v___x_2982_ = v___x_2980_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_dec(v___x_2980_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 0, v___x_2977_);
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2977_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
else
{
return v___x_2980_;
}
}
}
}
LEAN_EXPORT void l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2960_ = stack[0].m_obj;
uint8_t v_isMeta_2961_ = stack[1].m_num;
lean_object* v___y_2962_ = stack[2].m_obj;
lean_object* v___y_2963_ = stack[3].m_obj;
lean_object* v___y_2964_ = stack[4].m_obj;
lean_object* v___y_2965_ = stack[5].m_obj;
lean_object* v___y_2966_ = stack[6].m_obj;
lean_object* v___y_2967_ = stack[7].m_obj;
lean_object* v_res_3012_;
v_res_3012_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(v_declName_2960_, v_isMeta_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
stack->m_obj
 = v_res_3012_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___boxed(lean_object* v_declName_3013_, lean_object* v_isMeta_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
uint8_t v_isMeta_boxed_3022_; lean_object* v_res_3023_; 
v_isMeta_boxed_3022_ = lean_unbox(v_isMeta_3014_);
v_res_3023_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(v_declName_3013_, v_isMeta_boxed_3022_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
return v_res_3023_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(lean_object* v_as_x27_3024_, lean_object* v_b_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
if (lean_obj_tag(v_as_x27_3024_) == 0)
{
lean_object* v___x_3033_; 
v___x_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3033_, 0, v_b_3025_);
return v___x_3033_;
}
else
{
lean_object* v_head_3034_; lean_object* v_tail_3035_; lean_object* v___x_3036_; uint8_t v___x_3037_; lean_object* v___x_3038_; 
v_head_3034_ = lean_ctor_get(v_as_x27_3024_, 0);
v_tail_3035_ = lean_ctor_get(v_as_x27_3024_, 1);
v___x_3036_ = lean_box(0);
v___x_3037_ = 1;
lean_inc(v_head_3034_);
v___x_3038_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(v_head_3034_, v___x_3037_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_dec_ref_known(v___x_3038_, 1);
v_as_x27_3024_ = v_tail_3035_;
v_b_3025_ = v___x_3036_;
goto _start;
}
else
{
return v___x_3038_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_3024_ = stack[0].m_obj;
lean_object* v_b_3025_ = stack[1].m_obj;
lean_object* v___y_3026_ = stack[2].m_obj;
lean_object* v___y_3027_ = stack[3].m_obj;
lean_object* v___y_3028_ = stack[4].m_obj;
lean_object* v___y_3029_ = stack[5].m_obj;
lean_object* v___y_3030_ = stack[6].m_obj;
lean_object* v___y_3031_ = stack[7].m_obj;
lean_object* v_res_3040_;
v_res_3040_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_as_x27_3024_, v_b_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
stack->m_obj
 = v_res_3040_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_3041_, lean_object* v_b_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_as_x27_3041_, v_b_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec(v_as_x27_3041_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4(lean_object* v_env_3051_, lean_object* v_currNamespace_3052_, lean_object* v_openDecls_3053_, lean_object* v_n_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = l_Lean_ResolveName_resolveNamespace(v_env_3051_, v_currNamespace_3052_, v_openDecls_3053_, v_n_3054_);
v___x_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
lean_ctor_set(v___x_3058_, 1, v___y_3056_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4___boxed(lean_object* v_env_3059_, lean_object* v_currNamespace_3060_, lean_object* v_openDecls_3061_, lean_object* v_n_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4(v_env_3059_, v_currNamespace_3060_, v_openDecls_3061_, v_n_3062_, v___y_3063_, v___y_3064_);
lean_dec_ref(v___y_3063_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2(lean_object* v_currNamespace_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3069_, 0, v_currNamespace_3066_);
lean_ctor_set(v___x_3069_, 1, v___y_3068_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2___boxed(lean_object* v_currNamespace_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2(v_currNamespace_3070_, v___y_3071_, v___y_3072_);
lean_dec_ref(v___y_3071_);
return v_res_3073_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = lean_box(0);
v___x_3075_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
lean_ctor_set(v___x_3076_, 1, v___x_3074_);
return v___x_3076_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg(){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0);
v___x_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
return v___x_3079_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3080_;
v_res_3080_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
stack->m_obj
 = v_res_3080_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___boxed(lean_object* v___y_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
return v_res_3082_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3088_ = l_Lean_maxRecDepthErrorMessage;
v___x_3089_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3088_);
return v___x_3089_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3);
v___x_3091_ = l_Lean_MessageData_ofFormat(v___x_3090_);
return v___x_3091_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4);
v___x_3093_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__2));
v___x_3094_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
lean_ctor_set(v___x_3094_, 1, v___x_3092_);
return v___x_3094_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(lean_object* v_ref_3095_){
_start:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3097_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5);
v___x_3098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3098_, 0, v_ref_3095_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
return v___x_3099_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3095_ = stack[0].m_obj;
lean_object* v_res_3100_;
v_res_3100_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_ref_3095_);
stack->m_obj
 = v_res_3100_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___boxed(lean_object* v_ref_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_ref_3101_);
return v_res_3103_;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(lean_object* v_x_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
lean_object* v___x_3113_; lean_object* v_toCold_3114_; lean_object* v_env_3115_; lean_object* v_currRecDepth_3116_; lean_object* v_ref_3117_; lean_object* v_maxRecDepth_3118_; lean_object* v_currNamespace_3119_; lean_object* v_openDecls_3120_; lean_object* v_quotContext_3121_; lean_object* v_currMacroScope_3122_; lean_object* v___f_3123_; lean_object* v___f_3124_; lean_object* v___x_3125_; lean_object* v___f_3126_; lean_object* v___f_3127_; lean_object* v___f_3128_; lean_object* v_methods_3129_; lean_object* v___x_3130_; lean_object* v_nextMacroScope_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3113_ = lean_st_ref_get(v___y_3111_);
v_toCold_3114_ = lean_ctor_get(v___y_3110_, 0);
v_env_3115_ = lean_ctor_get(v___x_3113_, 0);
lean_inc_ref_n(v_env_3115_, 4);
lean_dec(v___x_3113_);
v_currRecDepth_3116_ = lean_ctor_get(v___y_3110_, 1);
v_ref_3117_ = lean_ctor_get(v___y_3110_, 2);
v_maxRecDepth_3118_ = lean_ctor_get(v_toCold_3114_, 3);
v_currNamespace_3119_ = lean_ctor_get(v_toCold_3114_, 4);
v_openDecls_3120_ = lean_ctor_get(v_toCold_3114_, 5);
v_quotContext_3121_ = lean_ctor_get(v_toCold_3114_, 8);
v_currMacroScope_3122_ = lean_ctor_get(v_toCold_3114_, 9);
v___f_3123_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3123_, 0, v_env_3115_);
v___f_3124_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_3124_, 0, v_env_3115_);
v___x_3125_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3110_);
lean_inc_n(v_currNamespace_3119_, 3);
v___f_3126_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3126_, 0, v_currNamespace_3119_);
lean_inc_n(v_openDecls_3120_, 2);
v___f_3127_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_3127_, 0, v_env_3115_);
lean_closure_set(v___f_3127_, 1, v___x_3125_);
lean_closure_set(v___f_3127_, 2, v_currNamespace_3119_);
lean_closure_set(v___f_3127_, 3, v_openDecls_3120_);
v___f_3128_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_3128_, 0, v_env_3115_);
lean_closure_set(v___f_3128_, 1, v_currNamespace_3119_);
lean_closure_set(v___f_3128_, 2, v_openDecls_3120_);
v_methods_3129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_3129_, 0, v___f_3124_);
lean_ctor_set(v_methods_3129_, 1, v___f_3126_);
lean_ctor_set(v_methods_3129_, 2, v___f_3123_);
lean_ctor_set(v_methods_3129_, 3, v___f_3128_);
lean_ctor_set(v_methods_3129_, 4, v___f_3127_);
v___x_3130_ = lean_st_ref_get(v___y_3111_);
v_nextMacroScope_3131_ = lean_ctor_get(v___x_3130_, 1);
lean_inc(v_nextMacroScope_3131_);
lean_dec(v___x_3130_);
lean_inc(v_ref_3117_);
lean_inc(v_maxRecDepth_3118_);
lean_inc(v_currRecDepth_3116_);
lean_inc(v_currMacroScope_3122_);
lean_inc(v_quotContext_3121_);
v___x_3132_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3132_, 0, v_methods_3129_);
lean_ctor_set(v___x_3132_, 1, v_quotContext_3121_);
lean_ctor_set(v___x_3132_, 2, v_currMacroScope_3122_);
lean_ctor_set(v___x_3132_, 3, v_currRecDepth_3116_);
lean_ctor_set(v___x_3132_, 4, v_maxRecDepth_3118_);
lean_ctor_set(v___x_3132_, 5, v_ref_3117_);
v___x_3133_ = lean_box(0);
v___x_3134_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3134_, 0, v_nextMacroScope_3131_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
lean_ctor_set(v___x_3134_, 2, v___x_3133_);
v___x_3135_ = lean_apply_2(v_x_3105_, v___x_3132_, v___x_3134_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v_a_3137_; lean_object* v_macroScope_3138_; lean_object* v_traceMsgs_3139_; lean_object* v_expandedMacroDecls_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 1);
lean_inc(v_a_3136_);
v_a_3137_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3137_);
lean_dec_ref_known(v___x_3135_, 2);
v_macroScope_3138_ = lean_ctor_get(v_a_3136_, 0);
lean_inc(v_macroScope_3138_);
v_traceMsgs_3139_ = lean_ctor_get(v_a_3136_, 1);
lean_inc(v_traceMsgs_3139_);
v_expandedMacroDecls_3140_ = lean_ctor_get(v_a_3136_, 2);
lean_inc(v_expandedMacroDecls_3140_);
lean_dec(v_a_3136_);
v___x_3141_ = lean_box(0);
v___x_3142_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_expandedMacroDecls_3140_, v___x_3141_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
lean_dec(v_expandedMacroDecls_3140_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v___x_3143_; lean_object* v_env_3144_; lean_object* v_ngen_3145_; lean_object* v_auxDeclNGen_3146_; lean_object* v_traceState_3147_; lean_object* v_cache_3148_; lean_object* v_recordedDeps_3149_; lean_object* v_messages_3150_; lean_object* v_infoState_3151_; lean_object* v_snapshotTasks_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3178_; 
lean_dec_ref_known(v___x_3142_, 1);
v___x_3143_ = lean_st_ref_take(v___y_3111_);
v_env_3144_ = lean_ctor_get(v___x_3143_, 0);
v_ngen_3145_ = lean_ctor_get(v___x_3143_, 2);
v_auxDeclNGen_3146_ = lean_ctor_get(v___x_3143_, 3);
v_traceState_3147_ = lean_ctor_get(v___x_3143_, 4);
v_cache_3148_ = lean_ctor_get(v___x_3143_, 5);
v_recordedDeps_3149_ = lean_ctor_get(v___x_3143_, 6);
v_messages_3150_ = lean_ctor_get(v___x_3143_, 7);
v_infoState_3151_ = lean_ctor_get(v___x_3143_, 8);
v_snapshotTasks_3152_ = lean_ctor_get(v___x_3143_, 9);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3178_ == 0)
{
lean_object* v_unused_3179_; 
v_unused_3179_ = lean_ctor_get(v___x_3143_, 1);
lean_dec(v_unused_3179_);
v___x_3154_ = v___x_3143_;
v_isShared_3155_ = v_isSharedCheck_3178_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_snapshotTasks_3152_);
lean_inc(v_infoState_3151_);
lean_inc(v_messages_3150_);
lean_inc(v_recordedDeps_3149_);
lean_inc(v_cache_3148_);
lean_inc(v_traceState_3147_);
lean_inc(v_auxDeclNGen_3146_);
lean_inc(v_ngen_3145_);
lean_inc(v_env_3144_);
lean_dec(v___x_3143_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3178_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 1, v_macroScope_3138_);
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_env_3144_);
lean_ctor_set(v_reuseFailAlloc_3177_, 1, v_macroScope_3138_);
lean_ctor_set(v_reuseFailAlloc_3177_, 2, v_ngen_3145_);
lean_ctor_set(v_reuseFailAlloc_3177_, 3, v_auxDeclNGen_3146_);
lean_ctor_set(v_reuseFailAlloc_3177_, 4, v_traceState_3147_);
lean_ctor_set(v_reuseFailAlloc_3177_, 5, v_cache_3148_);
lean_ctor_set(v_reuseFailAlloc_3177_, 6, v_recordedDeps_3149_);
lean_ctor_set(v_reuseFailAlloc_3177_, 7, v_messages_3150_);
lean_ctor_set(v_reuseFailAlloc_3177_, 8, v_infoState_3151_);
lean_ctor_set(v_reuseFailAlloc_3177_, 9, v_snapshotTasks_3152_);
v___x_3157_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3158_ = lean_st_ref_put(v___y_3111_, v___x_3157_);
v___x_3159_ = l_List_reverse___redArg(v_traceMsgs_3139_);
v___x_3160_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(v___x_3159_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3167_ == 0)
{
lean_object* v_unused_3168_; 
v_unused_3168_ = lean_ctor_get(v___x_3160_, 0);
lean_dec(v_unused_3168_);
v___x_3162_ = v___x_3160_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_dec(v___x_3160_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 0, v_a_3137_);
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3137_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
lean_dec(v_a_3137_);
v_a_3169_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_3160_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3160_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
}
}
else
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3187_; 
lean_dec(v_traceMsgs_3139_);
lean_dec(v_macroScope_3138_);
lean_dec(v_a_3137_);
v_a_3180_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3182_ = v___x_3142_;
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3142_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3180_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
}
else
{
lean_object* v_a_3188_; 
v_a_3188_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3188_);
lean_dec_ref_known(v___x_3135_, 2);
if (lean_obj_tag(v_a_3188_) == 0)
{
lean_object* v_a_3189_; lean_object* v_a_3190_; lean_object* v___x_3191_; uint8_t v___x_3192_; 
v_a_3189_ = lean_ctor_get(v_a_3188_, 0);
lean_inc(v_a_3189_);
v_a_3190_ = lean_ctor_get(v_a_3188_, 1);
lean_inc_ref(v_a_3190_);
lean_dec_ref_known(v_a_3188_, 2);
v___x_3191_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___closed__0));
v___x_3192_ = lean_string_dec_eq(v_a_3190_, v___x_3191_);
if (v___x_3192_ == 0)
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3193_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3193_, 0, v_a_3190_);
v___x_3194_ = l_Lean_MessageData_ofFormat(v___x_3193_);
v___x_3195_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_a_3189_, v___x_3194_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
lean_dec(v_a_3189_);
return v___x_3195_;
}
else
{
lean_object* v___x_3196_; 
lean_dec_ref(v_a_3190_);
v___x_3196_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_a_3189_);
return v___x_3196_;
}
}
else
{
lean_object* v___x_3197_; 
v___x_3197_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
return v___x_3197_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3105_ = stack[0].m_obj;
lean_object* v___y_3106_ = stack[1].m_obj;
lean_object* v___y_3107_ = stack[2].m_obj;
lean_object* v___y_3108_ = stack[3].m_obj;
lean_object* v___y_3109_ = stack[4].m_obj;
lean_object* v___y_3110_ = stack[5].m_obj;
lean_object* v___y_3111_ = stack[6].m_obj;
lean_object* v_res_3198_;
v_res_3198_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v_x_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
stack->m_obj
 = v_res_3198_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___boxed(lean_object* v_x_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v_x_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
return v_res_3207_;
}
}
lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(lean_object* v_pre_3208_, lean_object* v_binders_3209_, lean_object* v_type_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_){
_start:
{
lean_object* v___y_3219_; lean_object* v___f_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
lean_inc_ref(v_pre_3208_);
v___f_3223_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1___boxed), 10, 2);
lean_closure_set(v___f_3223_, 0, v_type_3210_);
lean_closure_set(v___f_3223_, 1, v_pre_3208_);
v___x_3224_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___boxed), 10, 3);
lean_closure_set(v___x_3224_, 0, lean_box(0));
lean_closure_set(v___x_3224_, 1, v_binders_3209_);
lean_closure_set(v___x_3224_, 2, v___f_3223_);
v___x_3225_ = l_Lean_Elab_Term_withAutoBoundImplicit___redArg(v___x_3224_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_dec_ref(v_pre_3208_);
v___y_3219_ = v___x_3225_;
goto v___jp_3218_;
}
else
{
lean_object* v_a_3226_; uint8_t v___y_3228_; uint8_t v___x_3232_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v___x_3232_ = l_Lean_Exception_isInterrupt(v_a_3226_);
if (v___x_3232_ == 0)
{
uint8_t v___x_3233_; 
lean_inc(v_a_3226_);
v___x_3233_ = l_Lean_Exception_isRuntime(v_a_3226_);
v___y_3228_ = v___x_3233_;
goto v___jp_3227_;
}
else
{
v___y_3228_ = v___x_3232_;
goto v___jp_3227_;
}
v___jp_3227_:
{
if (v___y_3228_ == 0)
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
lean_dec_ref_known(v___x_3225_, 1);
v___x_3229_ = lean_box(0);
v___x_3230_ = l_Lean_Name_str___override(v___x_3229_, v_pre_3208_);
v___x_3231_ = l_Lean_Core_mkFreshUserName(v___x_3230_, v_a_3215_, v_a_3216_);
v___y_3219_ = v___x_3231_;
goto v___jp_3218_;
}
else
{
lean_dec_ref(v_pre_3208_);
v___y_3219_ = v___x_3225_;
goto v___jp_3218_;
}
}
}
v___jp_3218_:
{
if (lean_obj_tag(v___y_3219_) == 0)
{
lean_object* v_a_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v_a_3220_ = lean_ctor_get(v___y_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref_known(v___y_3219_, 1);
v___x_3221_ = lean_alloc_closure((void*)(l_Lean_Elab_mkUnusedBaseName___boxed), 3, 1);
lean_closure_set(v___x_3221_, 0, v_a_3220_);
v___x_3222_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v___x_3221_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
return v___x_3222_;
}
else
{
return v___y_3219_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_3208_ = stack[0].m_obj;
lean_object* v_binders_3209_ = stack[1].m_obj;
lean_object* v_type_3210_ = stack[2].m_obj;
lean_object* v_a_3211_ = stack[3].m_obj;
lean_object* v_a_3212_ = stack[4].m_obj;
lean_object* v_a_3213_ = stack[5].m_obj;
lean_object* v_a_3214_ = stack[6].m_obj;
lean_object* v_a_3215_ = stack[7].m_obj;
lean_object* v_a_3216_ = stack[8].m_obj;
lean_object* v_res_3234_;
v_res_3234_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(v_pre_3208_, v_binders_3209_, v_type_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
stack->m_obj
 = v_res_3234_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___boxed(lean_object* v_pre_3235_, lean_object* v_binders_3236_, lean_object* v_type_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(v_pre_3235_, v_binders_3236_, v_type_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_);
lean_dec(v_a_3243_);
lean_dec_ref(v_a_3242_);
lean_dec(v_a_3241_);
lean_dec_ref(v_a_3240_);
lean_dec(v_a_3239_);
lean_dec_ref(v_a_3238_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2(lean_object* v_00_u03b1_3246_, lean_object* v_x_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v___x_3250_; 
v___x_3250_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v_x_3247_, v___y_3249_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3251_, lean_object* v_x_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2(v_00_u03b1_3251_, v_x_3252_, v___y_3253_, v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec_ref(v_x_3252_);
return v_res_3255_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7(lean_object* v_00_u03b1_3256_, lean_object* v_ref_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
lean_object* v___x_3265_; 
v___x_3265_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_ref_3257_);
return v___x_3265_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3257_ = stack[1].m_obj;
lean_object* v___y_3258_ = stack[2].m_obj;
lean_object* v___y_3259_ = stack[3].m_obj;
lean_object* v___y_3260_ = stack[4].m_obj;
lean_object* v___y_3261_ = stack[5].m_obj;
lean_object* v___y_3262_ = stack[6].m_obj;
lean_object* v___y_3263_ = stack[7].m_obj;
lean_object* v_res_3266_;
v_res_3266_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7(lean_box(0), v_ref_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_);
stack->m_obj
 = v_res_3266_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___boxed(lean_object* v_00_u03b1_3267_, lean_object* v_ref_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7(v_00_u03b1_3267_, v_ref_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
return v_res_3276_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8(lean_object* v_00_u03b1_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v___x_3285_; 
v___x_3285_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
return v___x_3285_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3278_ = stack[1].m_obj;
lean_object* v___y_3279_ = stack[2].m_obj;
lean_object* v___y_3280_ = stack[3].m_obj;
lean_object* v___y_3281_ = stack[4].m_obj;
lean_object* v___y_3282_ = stack[5].m_obj;
lean_object* v___y_3283_ = stack[6].m_obj;
lean_object* v_res_3286_;
v_res_3286_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8(lean_box(0), v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
stack->m_obj
 = v_res_3286_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___boxed(lean_object* v_00_u03b1_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8(v_00_u03b1_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
return v_res_3295_;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1(lean_object* v_00_u03b1_3296_, lean_object* v_x_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v_x_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
return v___x_3305_;
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3297_ = stack[1].m_obj;
lean_object* v___y_3298_ = stack[2].m_obj;
lean_object* v___y_3299_ = stack[3].m_obj;
lean_object* v___y_3300_ = stack[4].m_obj;
lean_object* v___y_3301_ = stack[5].m_obj;
lean_object* v___y_3302_ = stack[6].m_obj;
lean_object* v___y_3303_ = stack[7].m_obj;
lean_object* v_res_3306_;
v_res_3306_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1(lean_box(0), v_x_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
stack->m_obj
 = v_res_3306_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___boxed(lean_object* v_00_u03b1_3307_, lean_object* v_x_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1(v_00_u03b1_3307_, v_x_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
return v_res_3316_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1(lean_object* v_cls_3317_, lean_object* v_msg_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v___x_3326_; 
v___x_3326_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_3317_, v_msg_3318_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
return v___x_3326_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3317_ = stack[0].m_obj;
lean_object* v_msg_3318_ = stack[1].m_obj;
lean_object* v___y_3319_ = stack[2].m_obj;
lean_object* v___y_3320_ = stack[3].m_obj;
lean_object* v___y_3321_ = stack[4].m_obj;
lean_object* v___y_3322_ = stack[5].m_obj;
lean_object* v___y_3323_ = stack[6].m_obj;
lean_object* v___y_3324_ = stack[7].m_obj;
lean_object* v_res_3327_;
v_res_3327_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1(v_cls_3317_, v_msg_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
stack->m_obj
 = v_res_3327_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___boxed(lean_object* v_cls_3328_, lean_object* v_msg_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_){
_start:
{
lean_object* v_res_3337_; 
v_res_3337_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1(v_cls_3328_, v_msg_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
return v_res_3337_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4(lean_object* v_as_3338_, lean_object* v_as_x27_3339_, lean_object* v_b_3340_, lean_object* v_a_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v___x_3349_; 
v___x_3349_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_as_x27_3339_, v_b_3340_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
return v___x_3349_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3338_ = stack[0].m_obj;
lean_object* v_as_x27_3339_ = stack[1].m_obj;
lean_object* v_b_3340_ = stack[2].m_obj;
lean_object* v___y_3342_ = stack[4].m_obj;
lean_object* v___y_3343_ = stack[5].m_obj;
lean_object* v___y_3344_ = stack[6].m_obj;
lean_object* v___y_3345_ = stack[7].m_obj;
lean_object* v___y_3346_ = stack[8].m_obj;
lean_object* v___y_3347_ = stack[9].m_obj;
lean_object* v_res_3350_;
v_res_3350_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4(v_as_3338_, v_as_x27_3339_, v_b_3340_, lean_box(0), v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
stack->m_obj
 = v_res_3350_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___boxed(lean_object* v_as_3351_, lean_object* v_as_x27_3352_, lean_object* v_b_3353_, lean_object* v_a_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4(v_as_3351_, v_as_x27_3352_, v_b_3353_, v_a_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v_as_x27_3352_);
lean_dec(v_as_3351_);
return v_res_3362_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6(lean_object* v_00_u03b1_3363_, lean_object* v_ref_3364_, lean_object* v_msg_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_ref_3364_, v_msg_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
return v___x_3373_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3364_ = stack[1].m_obj;
lean_object* v_msg_3365_ = stack[2].m_obj;
lean_object* v___y_3366_ = stack[3].m_obj;
lean_object* v___y_3367_ = stack[4].m_obj;
lean_object* v___y_3368_ = stack[5].m_obj;
lean_object* v___y_3369_ = stack[6].m_obj;
lean_object* v___y_3370_ = stack[7].m_obj;
lean_object* v___y_3371_ = stack[8].m_obj;
lean_object* v_res_3374_;
v_res_3374_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6(lean_box(0), v_ref_3364_, v_msg_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
stack->m_obj
 = v_res_3374_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3375_, lean_object* v_ref_3376_, lean_object* v_msg_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v_res_3385_; 
v_res_3385_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6(v_00_u03b1_3375_, v_ref_3376_, v_msg_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v_ref_3376_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_3386_, lean_object* v_m_3387_, lean_object* v_a_3388_){
_start:
{
lean_object* v___x_3389_; 
v___x_3389_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(v_m_3387_, v_a_3388_);
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3390_, lean_object* v_m_3391_, lean_object* v_a_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6(v_00_u03b2_3390_, v_m_3391_, v_a_3392_);
lean_dec(v_a_3392_);
lean_dec_ref(v_m_3391_);
return v_res_3393_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10(lean_object* v_00_u03b1_3394_, lean_object* v_msg_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v___x_3403_; 
v___x_3403_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
return v___x_3403_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3395_ = stack[1].m_obj;
lean_object* v___y_3396_ = stack[2].m_obj;
lean_object* v___y_3397_ = stack[3].m_obj;
lean_object* v___y_3398_ = stack[4].m_obj;
lean_object* v___y_3399_ = stack[5].m_obj;
lean_object* v___y_3400_ = stack[6].m_obj;
lean_object* v___y_3401_ = stack[7].m_obj;
lean_object* v_res_3404_;
v_res_3404_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10(lean_box(0), v_msg_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
stack->m_obj
 = v_res_3404_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___boxed(lean_object* v_00_u03b1_3405_, lean_object* v_msg_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
lean_object* v_res_3414_; 
v_res_3414_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10(v_00_u03b1_3405_, v_msg_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
return v_res_3414_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_3415_, lean_object* v_x_3416_, lean_object* v_x_3417_){
_start:
{
uint8_t v___x_3418_; 
v___x_3418_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v_x_3416_, v_x_3417_);
return v___x_3418_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3416_ = stack[1].m_obj;
lean_object* v_x_3417_ = stack[2].m_obj;
uint8_t v_res_3419_;
v_res_3419_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7(lean_box(0), v_x_3416_, v_x_3417_);
stack->m_num = v_res_3419_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3420_, lean_object* v_x_3421_, lean_object* v_x_3422_){
_start:
{
uint8_t v_res_3423_; lean_object* v_r_3424_; 
v_res_3423_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7(v_00_u03b2_3420_, v_x_3421_, v_x_3422_);
lean_dec_ref(v_x_3422_);
lean_dec_ref(v_x_3421_);
v_r_3424_ = lean_box(v_res_3423_);
return v_r_3424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_3425_, lean_object* v_a_3426_, lean_object* v_x_3427_){
_start:
{
lean_object* v___x_3428_; 
v___x_3428_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(v_a_3426_, v_x_3427_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_3429_, lean_object* v_a_3430_, lean_object* v_x_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_3429_, v_a_3430_, v_x_3431_);
lean_dec(v_x_3431_);
lean_dec(v_a_3430_);
return v_res_3432_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15(lean_object* v_msgData_3433_, lean_object* v_macroStack_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v___x_3442_; 
v___x_3442_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_msgData_3433_, v_macroStack_3434_, v___y_3439_);
return v___x_3442_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_3433_ = stack[0].m_obj;
lean_object* v_macroStack_3434_ = stack[1].m_obj;
lean_object* v___y_3435_ = stack[2].m_obj;
lean_object* v___y_3436_ = stack[3].m_obj;
lean_object* v___y_3437_ = stack[4].m_obj;
lean_object* v___y_3438_ = stack[5].m_obj;
lean_object* v___y_3439_ = stack[6].m_obj;
lean_object* v___y_3440_ = stack[7].m_obj;
lean_object* v_res_3443_;
v_res_3443_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15(v_msgData_3433_, v_macroStack_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
stack->m_obj
 = v_res_3443_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___boxed(lean_object* v_msgData_3444_, lean_object* v_macroStack_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
lean_object* v_res_3453_; 
v_res_3453_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15(v_msgData_3444_, v_macroStack_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
return v_res_3453_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_3454_, lean_object* v_x_3455_, size_t v_x_3456_, lean_object* v_x_3457_){
_start:
{
uint8_t v___x_3458_; 
v___x_3458_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_3455_, v_x_3456_, v_x_3457_);
return v___x_3458_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3455_ = stack[1].m_obj;
size_t v_x_3456_ = stack[2].m_num;
lean_object* v_x_3457_ = stack[3].m_obj;
uint8_t v_res_3459_;
v_res_3459_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11(lean_box(0), v_x_3455_, v_x_3456_, v_x_3457_);
stack->m_num = v_res_3459_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3460_, lean_object* v_x_3461_, lean_object* v_x_3462_, lean_object* v_x_3463_){
_start:
{
size_t v_x_16893__boxed_3464_; uint8_t v_res_3465_; lean_object* v_r_3466_; 
v_x_16893__boxed_3464_ = lean_unbox_usize(v_x_3462_);
lean_dec(v_x_3462_);
v_res_3465_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11(v_00_u03b2_3460_, v_x_3461_, v_x_16893__boxed_3464_, v_x_3463_);
lean_dec_ref(v_x_3463_);
lean_dec_ref(v_x_3461_);
v_r_3466_ = lean_box(v_res_3465_);
return v_r_3466_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15(lean_object* v_00_u03b2_3467_, lean_object* v_keys_3468_, lean_object* v_vals_3469_, lean_object* v_heq_3470_, lean_object* v_i_3471_, lean_object* v_k_3472_){
_start:
{
uint8_t v___x_3473_; 
v___x_3473_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_keys_3468_, v_i_3471_, v_k_3472_);
return v___x_3473_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_3468_ = stack[1].m_obj;
lean_object* v_vals_3469_ = stack[2].m_obj;
lean_object* v_i_3471_ = stack[4].m_obj;
lean_object* v_k_3472_ = stack[5].m_obj;
uint8_t v_res_3474_;
v_res_3474_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15(lean_box(0), v_keys_3468_, v_vals_3469_, lean_box(0), v_i_3471_, v_k_3472_);
stack->m_num = v_res_3474_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___boxed(lean_object* v_00_u03b2_3475_, lean_object* v_keys_3476_, lean_object* v_vals_3477_, lean_object* v_heq_3478_, lean_object* v_i_3479_, lean_object* v_k_3480_){
_start:
{
uint8_t v_res_3481_; lean_object* v_r_3482_; 
v_res_3481_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15(v_00_u03b2_3475_, v_keys_3476_, v_vals_3477_, v_heq_3478_, v_i_3479_, v_k_3480_);
lean_dec_ref(v_k_3480_);
lean_dec_ref(v_vals_3477_);
lean_dec_ref(v_keys_3476_);
v_r_3482_ = lean_box(v_res_3481_);
return v_r_3482_;
}
}
lean_object* l_Lean_Elab_Command_mkInstanceName___lam__0(lean_object* v_binders_3484_, lean_object* v_type_3485_, lean_object* v_x_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3494_ = ((lean_object*)(l_Lean_Elab_Command_mkInstanceName___lam__0___closed__0));
v___x_3495_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(v___x_3494_, v_binders_3484_, v_type_3485_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
return v___x_3495_;
}
}
LEAN_EXPORT void l_Lean_Elab_Command_mkInstanceName___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_binders_3484_ = stack[0].m_obj;
lean_object* v_type_3485_ = stack[1].m_obj;
lean_object* v_x_3486_ = stack[2].m_obj;
lean_object* v___y_3487_ = stack[3].m_obj;
lean_object* v___y_3488_ = stack[4].m_obj;
lean_object* v___y_3489_ = stack[5].m_obj;
lean_object* v___y_3490_ = stack[6].m_obj;
lean_object* v___y_3491_ = stack[7].m_obj;
lean_object* v___y_3492_ = stack[8].m_obj;
lean_object* v_res_3496_;
v_res_3496_ = l_Lean_Elab_Command_mkInstanceName___lam__0(v_binders_3484_, v_type_3485_, v_x_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
stack->m_obj
 = v_res_3496_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__0___boxed(lean_object* v_binders_3497_, lean_object* v_type_3498_, lean_object* v_x_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Lean_Elab_Command_mkInstanceName___lam__0(v_binders_3497_, v_type_3498_, v_x_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec_ref(v_x_3499_);
return v_res_3507_;
}
}
lean_object* l_Lean_Elab_Command_mkInstanceName___lam__1(lean_object* v_a_3508_, lean_object* v_val_3509_, lean_object* v_a_x3f_3510_){
_start:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3512_ = lean_box(0);
v___x_3513_ = lean_st_ref_swap(v_a_3508_, v_val_3509_);
lean_dec(v___x_3513_);
v___x_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3512_);
return v___x_3514_;
}
}
LEAN_EXPORT void l_Lean_Elab_Command_mkInstanceName___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3508_ = stack[0].m_obj;
lean_object* v_val_3509_ = stack[1].m_obj;
lean_object* v_a_x3f_3510_ = stack[2].m_obj;
lean_object* v_res_3515_;
v_res_3515_ = l_Lean_Elab_Command_mkInstanceName___lam__1(v_a_3508_, v_val_3509_, v_a_x3f_3510_);
stack->m_obj
 = v_res_3515_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__1___boxed(lean_object* v_a_3516_, lean_object* v_val_3517_, lean_object* v_a_x3f_3518_, lean_object* v___y_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_Lean_Elab_Command_mkInstanceName___lam__1(v_a_3516_, v_val_3517_, v_a_x3f_3518_);
lean_dec(v_a_x3f_3518_);
lean_dec(v_a_3516_);
return v_res_3520_;
}
}
lean_object* l_Lean_Elab_Command_mkInstanceName(lean_object* v_binders_3521_, lean_object* v_type_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_){
_start:
{
lean_object* v___f_3526_; lean_object* v___x_3527_; lean_object* v_r_3528_; 
v___f_3526_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkInstanceName___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3526_, 0, v_binders_3521_);
lean_closure_set(v___f_3526_, 1, v_type_3522_);
v___x_3527_ = lean_st_ref_get(v_a_3524_);
v_r_3528_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_3526_, v_a_3523_, v_a_3524_);
if (lean_obj_tag(v_r_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3545_; 
v_a_3529_ = lean_ctor_get(v_r_3528_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v_r_3528_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3531_ = v_r_3528_;
v_isShared_3532_ = v_isSharedCheck_3545_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v_r_3528_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3545_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
lean_inc(v_a_3529_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set_tag(v___x_3531_, 1);
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
lean_object* v___x_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
v___x_3535_ = l_Lean_Elab_Command_mkInstanceName___lam__1(v_a_3524_, v___x_3527_, v___x_3534_);
lean_dec_ref(v___x_3534_);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3542_ == 0)
{
lean_object* v_unused_3543_; 
v_unused_3543_ = lean_ctor_get(v___x_3535_, 0);
lean_dec(v_unused_3543_);
v___x_3537_ = v___x_3535_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_dec(v___x_3535_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v_a_3529_);
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3529_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
v_a_3546_ = lean_ctor_get(v_r_3528_, 0);
lean_inc(v_a_3546_);
lean_dec_ref_known(v_r_3528_, 1);
v___x_3547_ = lean_box(0);
v___x_3548_ = l_Lean_Elab_Command_mkInstanceName___lam__1(v_a_3524_, v___x_3527_, v___x_3547_);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3555_ == 0)
{
lean_object* v_unused_3556_; 
v_unused_3556_ = lean_ctor_get(v___x_3548_, 0);
lean_dec(v_unused_3556_);
v___x_3550_ = v___x_3548_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_dec(v___x_3548_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
lean_ctor_set_tag(v___x_3550_, 1);
lean_ctor_set(v___x_3550_, 0, v_a_3546_);
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3546_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_mkInstanceName_0interp(lean_interpreter_value* stack)
{
lean_object* v_binders_3521_ = stack[0].m_obj;
lean_object* v_type_3522_ = stack[1].m_obj;
lean_object* v_a_3523_ = stack[2].m_obj;
lean_object* v_a_3524_ = stack[3].m_obj;
lean_object* v_res_3557_;
v_res_3557_ = l_Lean_Elab_Command_mkInstanceName(v_binders_3521_, v_type_3522_, v_a_3523_, v_a_3524_);
stack->m_obj
 = v_res_3557_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___boxed(lean_object* v_binders_3558_, lean_object* v_type_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l_Lean_Elab_Command_mkInstanceName(v_binders_3558_, v_type_3559_, v_a_3560_, v_a_3561_);
lean_dec(v_a_3561_);
lean_dec_ref(v_a_3560_);
return v_res_3563_;
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
