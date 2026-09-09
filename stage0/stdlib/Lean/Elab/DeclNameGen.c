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
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
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
static const lean_closure_object l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1 = (const lean_object*)&l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
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
lean_object* v___x_166_; lean_object* v_env_167_; lean_object* v___x_168_; lean_object* v_toCold_169_; lean_object* v_mctx_170_; lean_object* v_lctx_171_; lean_object* v_options_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_166_ = lean_st_ref_get(v___y_164_);
v_env_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc_ref(v_env_167_);
lean_dec(v___x_166_);
v___x_168_ = lean_st_ref_get(v___y_162_);
v_toCold_169_ = lean_ctor_get(v___y_163_, 0);
v_mctx_170_ = lean_ctor_get(v___x_168_, 0);
lean_inc_ref(v_mctx_170_);
lean_dec(v___x_168_);
v_lctx_171_ = lean_ctor_get(v___y_161_, 2);
v_options_172_ = lean_ctor_get(v_toCold_169_, 2);
lean_inc_ref(v_options_172_);
lean_inc_ref(v_lctx_171_);
v___x_173_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_173_, 0, v_env_167_);
lean_ctor_set(v___x_173_, 1, v_mctx_170_);
lean_ctor_set(v___x_173_, 2, v_lctx_171_);
lean_ctor_set(v___x_173_, 3, v_options_172_);
v___x_174_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v_msgData_160_);
v___x_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0___boxed(lean_object* v_msgData_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msgData_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(lean_object* v_msg_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_ref_189_; lean_object* v___x_190_; lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_199_; 
v_ref_189_ = lean_ctor_get(v___y_186_, 2);
v___x_190_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msg_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
v_a_191_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_199_ == 0)
{
v___x_193_ = v___x_190_;
v_isShared_194_ = v_isSharedCheck_199_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_190_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_199_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_197_; 
lean_inc(v_ref_189_);
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v_ref_189_);
lean_ctor_set(v___x_195_, 1, v_a_191_);
if (v_isShared_194_ == 0)
{
lean_ctor_set_tag(v___x_193_, 1);
lean_ctor_set(v___x_193_, 0, v___x_195_);
v___x_197_ = v___x_193_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg___boxed(lean_object* v_msg_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v_msg_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
return v_res_206_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(lean_object* v_a_207_, lean_object* v_x_208_){
_start:
{
if (lean_obj_tag(v_x_208_) == 0)
{
uint8_t v___x_209_; 
v___x_209_ = 0;
return v___x_209_;
}
else
{
lean_object* v_key_210_; lean_object* v_tail_211_; uint8_t v___x_212_; 
v_key_210_ = lean_ctor_get(v_x_208_, 0);
v_tail_211_ = lean_ctor_get(v_x_208_, 2);
v___x_212_ = lean_expr_eqv(v_key_210_, v_a_207_);
if (v___x_212_ == 0)
{
v_x_208_ = v_tail_211_;
goto _start;
}
else
{
return v___x_212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg___boxed(lean_object* v_a_214_, lean_object* v_x_215_){
_start:
{
uint8_t v_res_216_; lean_object* v_r_217_; 
v_res_216_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_214_, v_x_215_);
lean_dec(v_x_215_);
lean_dec_ref(v_a_214_);
v_r_217_ = lean_box(v_res_216_);
return v_r_217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9___redArg(lean_object* v_x_218_, lean_object* v_x_219_){
_start:
{
if (lean_obj_tag(v_x_219_) == 0)
{
return v_x_218_;
}
else
{
lean_object* v_key_220_; lean_object* v_value_221_; lean_object* v_tail_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_245_; 
v_key_220_ = lean_ctor_get(v_x_219_, 0);
v_value_221_ = lean_ctor_get(v_x_219_, 1);
v_tail_222_ = lean_ctor_get(v_x_219_, 2);
v_isSharedCheck_245_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_245_ == 0)
{
v___x_224_ = v_x_219_;
v_isShared_225_ = v_isSharedCheck_245_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_tail_222_);
lean_inc(v_value_221_);
lean_inc(v_key_220_);
lean_dec(v_x_219_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_245_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; uint64_t v___x_227_; uint64_t v___x_228_; uint64_t v___x_229_; uint64_t v_fold_230_; uint64_t v___x_231_; uint64_t v___x_232_; uint64_t v___x_233_; size_t v___x_234_; size_t v___x_235_; size_t v___x_236_; size_t v___x_237_; size_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_226_ = lean_array_get_size(v_x_218_);
v___x_227_ = l_Lean_Expr_hash(v_key_220_);
v___x_228_ = 32ULL;
v___x_229_ = lean_uint64_shift_right(v___x_227_, v___x_228_);
v_fold_230_ = lean_uint64_xor(v___x_227_, v___x_229_);
v___x_231_ = 16ULL;
v___x_232_ = lean_uint64_shift_right(v_fold_230_, v___x_231_);
v___x_233_ = lean_uint64_xor(v_fold_230_, v___x_232_);
v___x_234_ = lean_uint64_to_usize(v___x_233_);
v___x_235_ = lean_usize_of_nat(v___x_226_);
v___x_236_ = ((size_t)1ULL);
v___x_237_ = lean_usize_sub(v___x_235_, v___x_236_);
v___x_238_ = lean_usize_land(v___x_234_, v___x_237_);
v___x_239_ = lean_array_uget_borrowed(v_x_218_, v___x_238_);
lean_inc(v___x_239_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 2, v___x_239_);
v___x_241_ = v___x_224_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_key_220_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_value_221_);
lean_ctor_set(v_reuseFailAlloc_244_, 2, v___x_239_);
v___x_241_ = v_reuseFailAlloc_244_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; 
v___x_242_ = lean_array_uset(v_x_218_, v___x_238_, v___x_241_);
v_x_218_ = v___x_242_;
v_x_219_ = v_tail_222_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6___redArg(lean_object* v_i_246_, lean_object* v_source_247_, lean_object* v_target_248_){
_start:
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = lean_array_get_size(v_source_247_);
v___x_250_ = lean_nat_dec_lt(v_i_246_, v___x_249_);
if (v___x_250_ == 0)
{
lean_dec_ref(v_source_247_);
lean_dec(v_i_246_);
return v_target_248_;
}
else
{
lean_object* v_es_251_; lean_object* v___x_252_; lean_object* v_source_253_; lean_object* v_target_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_es_251_ = lean_array_fget(v_source_247_, v_i_246_);
v___x_252_ = lean_box(0);
v_source_253_ = lean_array_fset(v_source_247_, v_i_246_, v___x_252_);
v_target_254_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9___redArg(v_target_248_, v_es_251_);
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = lean_nat_add(v_i_246_, v___x_255_);
lean_dec(v_i_246_);
v_i_246_ = v___x_256_;
v_source_247_ = v_source_253_;
v_target_248_ = v_target_254_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(lean_object* v_data_258_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v_nbuckets_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_259_ = lean_array_get_size(v_data_258_);
v___x_260_ = lean_unsigned_to_nat(2u);
v_nbuckets_261_ = lean_nat_mul(v___x_259_, v___x_260_);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_box(0);
v___x_264_ = lean_mk_array(v_nbuckets_261_, v___x_263_);
v___x_265_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6___redArg(v___x_262_, v_data_258_, v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(lean_object* v_a_266_, lean_object* v_b_267_, lean_object* v_x_268_){
_start:
{
if (lean_obj_tag(v_x_268_) == 0)
{
lean_dec(v_b_267_);
lean_dec_ref(v_a_266_);
return v_x_268_;
}
else
{
lean_object* v_key_269_; lean_object* v_value_270_; lean_object* v_tail_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_283_; 
v_key_269_ = lean_ctor_get(v_x_268_, 0);
v_value_270_ = lean_ctor_get(v_x_268_, 1);
v_tail_271_ = lean_ctor_get(v_x_268_, 2);
v_isSharedCheck_283_ = !lean_is_exclusive(v_x_268_);
if (v_isSharedCheck_283_ == 0)
{
v___x_273_ = v_x_268_;
v_isShared_274_ = v_isSharedCheck_283_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_tail_271_);
lean_inc(v_value_270_);
lean_inc(v_key_269_);
lean_dec(v_x_268_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_283_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
uint8_t v___x_275_; 
v___x_275_ = lean_expr_eqv(v_key_269_, v_a_266_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_276_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(v_a_266_, v_b_267_, v_tail_271_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 2, v___x_276_);
v___x_278_ = v___x_273_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_key_269_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_value_270_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v___x_276_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
else
{
lean_object* v___x_281_; 
lean_dec(v_value_270_);
lean_dec(v_key_269_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 1, v_b_267_);
lean_ctor_set(v___x_273_, 0, v_a_266_);
v___x_281_ = v___x_273_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_266_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_b_267_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v_tail_271_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(lean_object* v_m_284_, lean_object* v_a_285_, lean_object* v_b_286_){
_start:
{
lean_object* v_size_287_; lean_object* v_buckets_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_331_; 
v_size_287_ = lean_ctor_get(v_m_284_, 0);
v_buckets_288_ = lean_ctor_get(v_m_284_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v_m_284_);
if (v_isSharedCheck_331_ == 0)
{
v___x_290_ = v_m_284_;
v_isShared_291_ = v_isSharedCheck_331_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_buckets_288_);
lean_inc(v_size_287_);
lean_dec(v_m_284_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_331_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_292_; uint64_t v___x_293_; uint64_t v___x_294_; uint64_t v___x_295_; uint64_t v_fold_296_; uint64_t v___x_297_; uint64_t v___x_298_; uint64_t v___x_299_; size_t v___x_300_; size_t v___x_301_; size_t v___x_302_; size_t v___x_303_; size_t v___x_304_; lean_object* v_bkt_305_; uint8_t v___x_306_; 
v___x_292_ = lean_array_get_size(v_buckets_288_);
v___x_293_ = l_Lean_Expr_hash(v_a_285_);
v___x_294_ = 32ULL;
v___x_295_ = lean_uint64_shift_right(v___x_293_, v___x_294_);
v_fold_296_ = lean_uint64_xor(v___x_293_, v___x_295_);
v___x_297_ = 16ULL;
v___x_298_ = lean_uint64_shift_right(v_fold_296_, v___x_297_);
v___x_299_ = lean_uint64_xor(v_fold_296_, v___x_298_);
v___x_300_ = lean_uint64_to_usize(v___x_299_);
v___x_301_ = lean_usize_of_nat(v___x_292_);
v___x_302_ = ((size_t)1ULL);
v___x_303_ = lean_usize_sub(v___x_301_, v___x_302_);
v___x_304_ = lean_usize_land(v___x_300_, v___x_303_);
v_bkt_305_ = lean_array_uget_borrowed(v_buckets_288_, v___x_304_);
v___x_306_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_285_, v_bkt_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v_size_x27_308_; lean_object* v___x_309_; lean_object* v_buckets_x27_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_307_ = lean_unsigned_to_nat(1u);
v_size_x27_308_ = lean_nat_add(v_size_287_, v___x_307_);
lean_dec(v_size_287_);
lean_inc(v_bkt_305_);
v___x_309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_309_, 0, v_a_285_);
lean_ctor_set(v___x_309_, 1, v_b_286_);
lean_ctor_set(v___x_309_, 2, v_bkt_305_);
v_buckets_x27_310_ = lean_array_uset(v_buckets_288_, v___x_304_, v___x_309_);
v___x_311_ = lean_unsigned_to_nat(4u);
v___x_312_ = lean_nat_mul(v_size_x27_308_, v___x_311_);
v___x_313_ = lean_unsigned_to_nat(3u);
v___x_314_ = lean_nat_div(v___x_312_, v___x_313_);
lean_dec(v___x_312_);
v___x_315_ = lean_array_get_size(v_buckets_x27_310_);
v___x_316_ = lean_nat_dec_le(v___x_314_, v___x_315_);
lean_dec(v___x_314_);
if (v___x_316_ == 0)
{
lean_object* v_val_317_; lean_object* v___x_319_; 
v_val_317_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(v_buckets_x27_310_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 1, v_val_317_);
lean_ctor_set(v___x_290_, 0, v_size_x27_308_);
v___x_319_ = v___x_290_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_size_x27_308_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_val_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
else
{
lean_object* v___x_322_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 1, v_buckets_x27_310_);
lean_ctor_set(v___x_290_, 0, v_size_x27_308_);
v___x_322_ = v___x_290_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_size_x27_308_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_buckets_x27_310_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
else
{
lean_object* v___x_324_; lean_object* v_buckets_x27_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
lean_inc(v_bkt_305_);
v___x_324_ = lean_box(0);
v_buckets_x27_325_ = lean_array_uset(v_buckets_288_, v___x_304_, v___x_324_);
v___x_326_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(v_a_285_, v_b_286_, v_bkt_305_);
v___x_327_ = lean_array_uset(v_buckets_x27_325_, v___x_304_, v___x_326_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 1, v___x_327_);
v___x_329_ = v___x_290_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_size_287_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(lean_object* v_a_332_, lean_object* v_x_333_){
_start:
{
if (lean_obj_tag(v_x_333_) == 0)
{
lean_object* v___x_334_; 
v___x_334_ = lean_box(0);
return v___x_334_;
}
else
{
lean_object* v_key_335_; lean_object* v_value_336_; lean_object* v_tail_337_; uint8_t v___x_338_; 
v_key_335_ = lean_ctor_get(v_x_333_, 0);
v_value_336_ = lean_ctor_get(v_x_333_, 1);
v_tail_337_ = lean_ctor_get(v_x_333_, 2);
v___x_338_ = lean_expr_eqv(v_key_335_, v_a_332_);
if (v___x_338_ == 0)
{
v_x_333_ = v_tail_337_;
goto _start;
}
else
{
lean_object* v___x_340_; 
lean_inc(v_value_336_);
v___x_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_340_, 0, v_value_336_);
return v___x_340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg___boxed(lean_object* v_a_341_, lean_object* v_x_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(v_a_341_, v_x_342_);
lean_dec(v_x_342_);
lean_dec_ref(v_a_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(lean_object* v_m_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_buckets_346_; lean_object* v___x_347_; uint64_t v___x_348_; uint64_t v___x_349_; uint64_t v___x_350_; uint64_t v_fold_351_; uint64_t v___x_352_; uint64_t v___x_353_; uint64_t v___x_354_; size_t v___x_355_; size_t v___x_356_; size_t v___x_357_; size_t v___x_358_; size_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_buckets_346_ = lean_ctor_get(v_m_344_, 1);
v___x_347_ = lean_array_get_size(v_buckets_346_);
v___x_348_ = l_Lean_Expr_hash(v_a_345_);
v___x_349_ = 32ULL;
v___x_350_ = lean_uint64_shift_right(v___x_348_, v___x_349_);
v_fold_351_ = lean_uint64_xor(v___x_348_, v___x_350_);
v___x_352_ = 16ULL;
v___x_353_ = lean_uint64_shift_right(v_fold_351_, v___x_352_);
v___x_354_ = lean_uint64_xor(v_fold_351_, v___x_353_);
v___x_355_ = lean_uint64_to_usize(v___x_354_);
v___x_356_ = lean_usize_of_nat(v___x_347_);
v___x_357_ = ((size_t)1ULL);
v___x_358_ = lean_usize_sub(v___x_356_, v___x_357_);
v___x_359_ = lean_usize_land(v___x_355_, v___x_358_);
v___x_360_ = lean_array_uget_borrowed(v_buckets_346_, v___x_359_);
v___x_361_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(v_a_345_, v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg___boxed(lean_object* v_m_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v_m_362_, v_a_363_);
lean_dec_ref(v_a_363_);
lean_dec_ref(v_m_362_);
return v_res_364_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0(void){
_start:
{
lean_object* v___x_365_; lean_object* v_dummy_366_; 
v___x_365_ = lean_box(0);
v_dummy_366_ = l_Lean_Expr_sort___override(v___x_365_);
return v_dummy_366_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__0));
v___x_369_ = l_Lean_stringToMessageData(v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(lean_object* v_snd_370_, lean_object* v_args_371_, lean_object* v_a_372_, lean_object* v_____r_373_, lean_object* v_fty_374_, lean_object* v_j_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
if (lean_obj_tag(v_fty_374_) == 7)
{
lean_object* v_body_382_; uint8_t v_binderInfo_383_; lean_object* v___x_389_; uint8_t v_a_391_; uint8_t v___x_434_; 
v_body_382_ = lean_ctor_get(v_fty_374_, 2);
lean_inc_ref(v_body_382_);
v_binderInfo_383_ = lean_ctor_get_uint8(v_fty_374_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_fty_374_, 3);
v___x_389_ = lean_array_fget_borrowed(v_args_371_, v_a_372_);
v___x_434_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_383_);
if (v___x_434_ == 0)
{
uint8_t v___x_435_; 
v___x_435_ = l_Lean_Expr_isSort(v___x_389_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; 
lean_inc(v___x_389_);
v___x_436_ = l_Lean_Meta_isTypeFormer(v___x_389_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; uint8_t v___x_438_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_437_);
lean_dec_ref_known(v___x_436_, 1);
v___x_438_ = lean_unbox(v_a_437_);
lean_dec(v_a_437_);
v_a_391_ = v___x_438_;
goto v___jp_390_;
}
else
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
lean_dec_ref(v_body_382_);
lean_dec(v_snd_370_);
v_a_439_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___x_436_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_436_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
else
{
goto v___jp_384_;
}
}
else
{
v_a_391_ = v___x_434_;
goto v___jp_390_;
}
v___jp_384_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
lean_inc(v_j_375_);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v_j_375_);
lean_ctor_set(v___x_385_, 1, v_snd_370_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v_body_382_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
return v___x_388_;
}
v___jp_390_:
{
if (v_a_391_ == 0)
{
goto v___jp_384_;
}
else
{
lean_object* v___x_392_; 
lean_inc(v___x_389_);
v___x_392_ = l_Lean_Meta_isProof(v___x_389_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_425_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_425_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_425_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_425_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
uint8_t v___x_397_; 
v___x_397_ = lean_unbox(v_a_393_);
lean_dec(v_a_393_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; 
lean_del_object(v___x_395_);
lean_inc(v___x_389_);
v___x_398_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_389_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_410_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_410_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_410_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_410_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_403_ = l_Lean_Expr_app___override(v_snd_370_, v_a_399_);
lean_inc(v_j_375_);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v_j_375_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v_body_382_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_406_);
v___x_408_ = v___x_401_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_dec_ref(v_body_382_);
lean_dec(v_snd_370_);
v_a_411_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_398_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_398_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
lean_inc(v_j_375_);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v_j_375_);
lean_ctor_set(v___x_419_, 1, v_snd_370_);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v_body_382_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
v___x_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_421_);
v___x_423_ = v___x_395_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec_ref(v_body_382_);
lean_dec(v_snd_370_);
v_a_426_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_392_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_392_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1);
v___x_448_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v___x_447_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_458_; 
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_458_ == 0)
{
lean_object* v_unused_459_; 
v_unused_459_ = lean_ctor_get(v___x_448_, 0);
lean_dec(v_unused_459_);
v___x_450_ = v___x_448_;
v_isShared_451_ = v_isSharedCheck_458_;
goto v_resetjp_449_;
}
else
{
lean_dec(v___x_448_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_458_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_456_; 
lean_inc(v_j_375_);
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v_j_375_);
lean_ctor_set(v___x_452_, 1, v_snd_370_);
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v_fty_374_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_454_);
v___x_456_ = v___x_450_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_dec_ref(v_fty_374_);
lean_dec(v_snd_370_);
v_a_460_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_448_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_448_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(lean_object* v_upperBound_468_, lean_object* v_args_469_, lean_object* v_a_470_, lean_object* v_b_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v___y_479_; uint8_t v___x_501_; 
v___x_501_ = lean_nat_dec_lt(v_a_470_, v_upperBound_468_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
lean_dec(v_a_470_);
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v_b_471_);
return v___x_502_;
}
else
{
lean_object* v_snd_503_; lean_object* v_fst_504_; lean_object* v_fst_505_; lean_object* v_snd_506_; lean_object* v___y_508_; uint8_t v___x_520_; 
v_snd_503_ = lean_ctor_get(v_b_471_, 1);
lean_inc(v_snd_503_);
v_fst_504_ = lean_ctor_get(v_b_471_, 0);
lean_inc(v_fst_504_);
lean_dec_ref(v_b_471_);
v_fst_505_ = lean_ctor_get(v_snd_503_, 0);
lean_inc(v_fst_505_);
v_snd_506_ = lean_ctor_get(v_snd_503_, 1);
lean_inc(v_snd_506_);
lean_dec(v_snd_503_);
v___x_520_ = l_Lean_Expr_isForall(v_fst_504_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; uint8_t v_transparency_522_; uint8_t v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_521_ = l_Lean_Meta_Context_config(v___y_473_);
v_transparency_522_ = lean_ctor_get_uint8(v___x_521_, 9);
lean_dec_ref(v___x_521_);
v___x_523_ = 0;
v___x_524_ = lean_expr_instantiate_rev_range(v_fst_504_, v_fst_505_, v_a_470_, v_args_469_);
lean_dec(v_fst_505_);
lean_dec(v_fst_504_);
v___x_525_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_522_, v___x_523_);
if (v___x_525_ == 0)
{
lean_object* v_keyedConfig_526_; uint8_t v_trackZetaDelta_527_; lean_object* v_zetaDeltaSet_528_; lean_object* v_lctx_529_; lean_object* v_localInstances_530_; lean_object* v_defEqCtx_x3f_531_; lean_object* v_synthPendingDepth_532_; lean_object* v_customCanUnfoldPredicate_x3f_533_; uint8_t v_univApprox_534_; uint8_t v_inTypeClassResolution_535_; uint8_t v_cacheInferType_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_keyedConfig_526_ = lean_ctor_get(v___y_473_, 0);
v_trackZetaDelta_527_ = lean_ctor_get_uint8(v___y_473_, sizeof(void*)*7);
v_zetaDeltaSet_528_ = lean_ctor_get(v___y_473_, 1);
v_lctx_529_ = lean_ctor_get(v___y_473_, 2);
v_localInstances_530_ = lean_ctor_get(v___y_473_, 3);
v_defEqCtx_x3f_531_ = lean_ctor_get(v___y_473_, 4);
v_synthPendingDepth_532_ = lean_ctor_get(v___y_473_, 5);
v_customCanUnfoldPredicate_x3f_533_ = lean_ctor_get(v___y_473_, 6);
v_univApprox_534_ = lean_ctor_get_uint8(v___y_473_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_535_ = lean_ctor_get_uint8(v___y_473_, sizeof(void*)*7 + 2);
v_cacheInferType_536_ = lean_ctor_get_uint8(v___y_473_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_526_);
v___x_537_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_523_, v_keyedConfig_526_);
lean_inc(v_customCanUnfoldPredicate_x3f_533_);
lean_inc(v_synthPendingDepth_532_);
lean_inc(v_defEqCtx_x3f_531_);
lean_inc_ref(v_localInstances_530_);
lean_inc_ref(v_lctx_529_);
lean_inc(v_zetaDeltaSet_528_);
v___x_538_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v_zetaDeltaSet_528_);
lean_ctor_set(v___x_538_, 2, v_lctx_529_);
lean_ctor_set(v___x_538_, 3, v_localInstances_530_);
lean_ctor_set(v___x_538_, 4, v_defEqCtx_x3f_531_);
lean_ctor_set(v___x_538_, 5, v_synthPendingDepth_532_);
lean_ctor_set(v___x_538_, 6, v_customCanUnfoldPredicate_x3f_533_);
lean_ctor_set_uint8(v___x_538_, sizeof(void*)*7, v_trackZetaDelta_527_);
lean_ctor_set_uint8(v___x_538_, sizeof(void*)*7 + 1, v_univApprox_534_);
lean_ctor_set_uint8(v___x_538_, sizeof(void*)*7 + 2, v_inTypeClassResolution_535_);
lean_ctor_set_uint8(v___x_538_, sizeof(void*)*7 + 3, v_cacheInferType_536_);
lean_inc(v___y_476_);
lean_inc_ref(v___y_475_);
lean_inc(v___y_474_);
v___x_539_ = lean_whnf(v___x_524_, v___x_538_, v___y_474_, v___y_475_, v___y_476_);
v___y_508_ = v___x_539_;
goto v___jp_507_;
}
else
{
lean_object* v___x_540_; 
lean_inc(v___y_476_);
lean_inc_ref(v___y_475_);
lean_inc(v___y_474_);
lean_inc_ref(v___y_473_);
v___x_540_ = lean_whnf(v___x_524_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
v___y_508_ = v___x_540_;
goto v___jp_507_;
}
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_box(0);
v___x_542_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_snd_506_, v_args_469_, v_a_470_, v___x_541_, v_fst_504_, v_fst_505_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
lean_dec(v_fst_505_);
v___y_479_ = v___x_542_;
goto v___jp_478_;
}
v___jp_507_:
{
if (lean_obj_tag(v___y_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v_a_509_ = lean_ctor_get(v___y_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref_known(v___y_508_, 1);
v___x_510_ = lean_box(0);
v___x_511_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_snd_506_, v_args_469_, v_a_470_, v___x_510_, v_a_509_, v_a_470_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
v___y_479_ = v___x_511_;
goto v___jp_478_;
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec(v_snd_506_);
lean_dec(v_a_470_);
v_a_512_ = lean_ctor_get(v___y_508_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___y_508_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___y_508_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___y_508_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
v___jp_478_:
{
if (lean_obj_tag(v___y_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_492_; 
v_a_480_ = lean_ctor_get(v___y_479_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___y_479_);
if (v_isSharedCheck_492_ == 0)
{
v___x_482_ = v___y_479_;
v_isShared_483_ = v_isSharedCheck_492_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___y_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_492_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
if (lean_obj_tag(v_a_480_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_486_; 
lean_dec(v_a_470_);
v_a_484_ = lean_ctor_get(v_a_480_, 0);
lean_inc(v_a_484_);
lean_dec_ref_known(v_a_480_, 1);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v_a_484_);
v___x_486_ = v___x_482_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
lean_del_object(v___x_482_);
v_a_488_ = lean_ctor_get(v_a_480_, 0);
lean_inc(v_a_488_);
lean_dec_ref_known(v_a_480_, 1);
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = lean_nat_add(v_a_470_, v___x_489_);
lean_dec(v_a_470_);
v_a_470_ = v___x_490_;
v_b_471_ = v_a_488_;
goto _start;
}
}
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
lean_dec(v_a_470_);
v_a_493_ = lean_ctor_get(v___y_479_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___y_479_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___y_479_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___y_479_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v_x_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
if (lean_obj_tag(v_x_543_) == 5)
{
lean_object* v_fn_552_; lean_object* v_arg_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_fn_552_ = lean_ctor_get(v_x_543_, 0);
lean_inc_ref(v_fn_552_);
v_arg_553_ = lean_ctor_get(v_x_543_, 1);
lean_inc_ref(v_arg_553_);
lean_dec_ref_known(v_x_543_, 2);
v___x_554_ = lean_array_set(v_x_544_, v_x_545_, v_arg_553_);
v___x_555_ = lean_unsigned_to_nat(1u);
v___x_556_ = lean_nat_sub(v_x_545_, v___x_555_);
lean_dec(v_x_545_);
v_x_543_ = v_fn_552_;
v_x_544_ = v___x_554_;
v_x_545_ = v___x_556_;
goto _start;
}
else
{
lean_object* v___x_558_; 
lean_dec(v_x_545_);
lean_inc(v___y_550_);
lean_inc_ref(v___y_549_);
lean_inc(v___y_548_);
lean_inc_ref(v___y_547_);
lean_inc_ref(v_x_543_);
v___x_558_ = lean_infer_type(v_x_543_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_560_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_558_, 1);
v___x_560_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_x_543_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_561_);
lean_dec_ref_known(v___x_560_, 1);
v___x_562_ = lean_array_get_size(v_x_544_);
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v_a_561_);
v___x_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_565_, 0, v_a_559_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v___x_562_, v_x_544_, v___x_563_, v___x_565_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
lean_dec_ref(v_x_544_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_576_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_576_ == 0)
{
v___x_569_ = v___x_566_;
v_isShared_570_ = v_isSharedCheck_576_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_576_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v_snd_571_; lean_object* v_snd_572_; lean_object* v___x_574_; 
v_snd_571_ = lean_ctor_get(v_a_567_, 1);
lean_inc(v_snd_571_);
lean_dec(v_a_567_);
v_snd_572_ = lean_ctor_get(v_snd_571_, 1);
lean_inc(v_snd_572_);
lean_dec(v_snd_571_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v_snd_572_);
v___x_574_ = v___x_569_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_snd_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
v_a_577_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_566_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_566_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
else
{
lean_dec(v_a_559_);
lean_dec_ref(v_x_544_);
return v___x_560_;
}
}
else
{
lean_dec_ref(v_x_544_);
lean_dec_ref(v_x_543_);
return v___x_558_;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = l_Lean_Expr_bvar___override(v___x_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0(lean_object* v_body_587_, lean_object* v_binderName_588_, uint8_t v_binderInfo_589_, lean_object* v_binderType_590_, lean_object* v_arg_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_ty_x27_599_; uint8_t v___x_611_; 
v___x_611_ = l_Lean_Expr_hasLooseBVars(v_body_587_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; 
v___x_612_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_binderType_590_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
lean_dec_ref_known(v___x_612_, 1);
v_ty_x27_599_ = v_a_613_;
goto v___jp_598_;
}
else
{
lean_dec(v_binderName_588_);
return v___x_612_;
}
}
else
{
lean_object* v___x_614_; 
lean_dec_ref(v_binderType_590_);
v___x_614_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0);
v_ty_x27_599_ = v___x_614_;
goto v___jp_598_;
}
v___jp_598_:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_expr_instantiate1(v_body_587_, v_arg_591_);
v___x_601_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_600_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_610_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_610_ == 0)
{
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_606_ = l_Lean_Expr_forallE___override(v_binderName_588_, v_ty_x27_599_, v_a_602_, v_binderInfo_589_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_606_);
v___x_608_ = v___x_604_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
else
{
lean_dec_ref(v_ty_x27_599_);
lean_dec(v_binderName_588_);
return v___x_601_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___boxed(lean_object* v_body_615_, lean_object* v_binderName_616_, lean_object* v_binderInfo_617_, lean_object* v_binderType_618_, lean_object* v_arg_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
uint8_t v_binderInfo_15855__boxed_626_; lean_object* v_res_627_; 
v_binderInfo_15855__boxed_626_ = lean_unbox(v_binderInfo_617_);
v_res_627_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0(v_body_615_, v_binderName_616_, v_binderInfo_15855__boxed_626_, v_binderType_618_, v_arg_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v_arg_619_);
lean_dec_ref(v_body_615_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1___boxed(lean_object* v_body_628_, lean_object* v_arg_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1(v_body_628_, v_arg_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v_arg_629_);
lean_dec_ref(v_body_628_);
return v_res_636_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__2));
v___x_641_ = l_Lean_Level_param___override(v___x_640_);
return v___x_641_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3);
v___x_643_ = l_Lean_Expr_sort___override(v___x_642_);
return v___x_643_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_box(0);
v___x_645_ = l_Lean_Level_succ___override(v___x_644_);
return v___x_645_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5);
v___x_647_ = l_Lean_Expr_sort___override(v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(lean_object* v_e_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_a_656_; lean_object* v___y_662_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = lean_st_ref_get(v_a_649_);
v___x_665_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v___x_664_, v_e_648_);
lean_dec(v___x_664_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v___x_666_; 
lean_inc_ref(v_e_648_);
v___x_666_ = l_Lean_Meta_isProof(v_e_648_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; uint8_t v___x_668_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_666_, 1);
v___x_668_ = lean_unbox(v_a_667_);
lean_dec(v_a_667_);
if (v___x_668_ == 0)
{
switch(lean_obj_tag(v_e_648_))
{
case 5:
{
lean_object* v___x_669_; 
v___x_669_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg(v_e_648_, v_a_653_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_669_, 1);
if (lean_obj_tag(v_a_670_) == 1)
{
lean_object* v_val_671_; lean_object* v___x_672_; 
v_val_671_ = lean_ctor_get(v_a_670_, 0);
lean_inc(v_val_671_);
lean_dec_ref_known(v_a_670_, 1);
v___x_672_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_val_671_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
v___y_662_ = v___x_672_;
goto v___jp_661_;
}
else
{
lean_object* v_dummy_673_; lean_object* v_nargs_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
lean_dec(v_a_670_);
v_dummy_673_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0);
v_nargs_674_ = l_Lean_Expr_getAppNumArgs(v_e_648_);
lean_inc(v_nargs_674_);
v___x_675_ = lean_mk_array(v_nargs_674_, v_dummy_673_);
v___x_676_ = lean_unsigned_to_nat(1u);
v___x_677_ = lean_nat_sub(v_nargs_674_, v___x_676_);
lean_dec(v_nargs_674_);
lean_inc_ref(v_e_648_);
v___x_678_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(v_e_648_, v___x_675_, v___x_677_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
v___y_662_ = v___x_678_;
goto v___jp_661_;
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref_known(v_e_648_, 2);
v_a_679_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_669_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_669_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
case 7:
{
lean_object* v_binderName_687_; lean_object* v_binderType_688_; lean_object* v_body_689_; uint8_t v_binderInfo_690_; lean_object* v___x_691_; lean_object* v___f_692_; uint8_t v___x_693_; lean_object* v___x_694_; 
v_binderName_687_ = lean_ctor_get(v_e_648_, 0);
v_binderType_688_ = lean_ctor_get(v_e_648_, 1);
v_body_689_ = lean_ctor_get(v_e_648_, 2);
v_binderInfo_690_ = lean_ctor_get_uint8(v_e_648_, sizeof(void*)*3 + 8);
v___x_691_ = lean_box(v_binderInfo_690_);
lean_inc_ref_n(v_binderType_688_, 2);
lean_inc_n(v_binderName_687_, 2);
lean_inc_ref(v_body_689_);
v___f_692_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___boxed), 11, 4);
lean_closure_set(v___f_692_, 0, v_body_689_);
lean_closure_set(v___f_692_, 1, v_binderName_687_);
lean_closure_set(v___f_692_, 2, v___x_691_);
lean_closure_set(v___f_692_, 3, v_binderType_688_);
v___x_693_ = 0;
v___x_694_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(v_binderName_687_, v_binderInfo_690_, v_binderType_688_, v___f_692_, v___x_693_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
v___y_662_ = v___x_694_;
goto v___jp_661_;
}
case 6:
{
lean_object* v_binderName_695_; lean_object* v_binderType_696_; lean_object* v_body_697_; uint8_t v_binderInfo_698_; lean_object* v___x_699_; 
v_binderName_695_ = lean_ctor_get(v_e_648_, 0);
v_binderType_696_ = lean_ctor_get(v_e_648_, 1);
v_body_697_ = lean_ctor_get(v_e_648_, 2);
v_binderInfo_698_ = lean_ctor_get_uint8(v_e_648_, sizeof(void*)*3 + 8);
lean_inc_ref(v_e_648_);
v___x_699_ = l_Lean_Expr_etaExpandedStrict_x3f(v_e_648_);
if (lean_obj_tag(v___x_699_) == 1)
{
lean_object* v_val_700_; lean_object* v___x_701_; 
v_val_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_val_700_);
lean_dec_ref_known(v___x_699_, 1);
v___x_701_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_val_700_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
v___y_662_ = v___x_701_;
goto v___jp_661_;
}
else
{
lean_object* v___f_702_; uint8_t v___x_703_; lean_object* v___x_704_; 
lean_dec(v___x_699_);
lean_inc_ref(v_body_697_);
v___f_702_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1___boxed), 8, 1);
lean_closure_set(v___f_702_, 0, v_body_697_);
v___x_703_ = 0;
lean_inc_ref(v_binderType_696_);
lean_inc(v_binderName_695_);
v___x_704_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(v_binderName_695_, v_binderInfo_698_, v_binderType_696_, v___f_702_, v___x_703_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
v___y_662_ = v___x_704_;
goto v___jp_661_;
}
}
case 8:
{
lean_object* v_value_705_; lean_object* v_body_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v_value_705_ = lean_ctor_get(v_e_648_, 2);
v_body_706_ = lean_ctor_get(v_e_648_, 3);
v___x_707_ = lean_expr_instantiate1(v_body_706_, v_value_705_);
v___x_708_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_707_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
v___y_662_ = v___x_708_;
goto v___jp_661_;
}
case 3:
{
uint8_t v___x_709_; 
v___x_709_ = l_Lean_Expr_isProp(v_e_648_);
if (v___x_709_ == 0)
{
uint8_t v___x_710_; 
v___x_710_ = l_Lean_Expr_isType(v_e_648_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; 
v___x_711_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4);
v_a_656_ = v___x_711_;
goto v___jp_655_;
}
else
{
lean_object* v___x_712_; 
v___x_712_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6);
v_a_656_ = v___x_712_;
goto v___jp_655_;
}
}
else
{
lean_object* v___x_713_; 
v___x_713_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0);
v_a_656_ = v___x_713_;
goto v___jp_655_;
}
}
case 4:
{
lean_object* v_declName_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v_declName_714_ = lean_ctor_get(v_e_648_, 0);
v___x_715_ = lean_box(0);
lean_inc(v_declName_714_);
v___x_716_ = l_Lean_Expr_const___override(v_declName_714_, v___x_715_);
v_a_656_ = v___x_716_;
goto v___jp_655_;
}
case 10:
{
lean_object* v_expr_717_; lean_object* v___x_718_; 
v_expr_717_ = lean_ctor_get(v_e_648_, 1);
lean_inc_ref(v_expr_717_);
v___x_718_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_expr_717_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
v___y_662_ = v___x_718_;
goto v___jp_661_;
}
default: 
{
lean_object* v___x_719_; 
v___x_719_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0);
v_a_656_ = v___x_719_;
goto v___jp_655_;
}
}
}
else
{
lean_object* v___x_720_; 
v___x_720_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0);
v_a_656_ = v___x_720_;
goto v___jp_655_;
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec_ref(v_e_648_);
v_a_721_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_666_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_666_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
else
{
lean_object* v_val_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec_ref(v_e_648_);
v_val_729_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_665_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_val_729_);
lean_dec(v___x_665_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
lean_ctor_set_tag(v___x_731_, 0);
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_val_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
v___jp_655_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_657_ = lean_st_ref_take(v_a_649_);
lean_inc_ref(v_a_656_);
v___x_658_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v___x_657_, v_e_648_, v_a_656_);
v___x_659_ = lean_st_ref_put(v_a_649_, v___x_658_);
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v_a_656_);
return v___x_660_;
}
v___jp_661_:
{
if (lean_obj_tag(v___y_662_) == 0)
{
lean_object* v_a_663_; 
v_a_663_ = lean_ctor_get(v___y_662_, 0);
lean_inc(v_a_663_);
lean_dec_ref_known(v___y_662_, 1);
v_a_656_ = v_a_663_;
goto v___jp_655_;
}
else
{
lean_dec_ref(v_e_648_);
return v___y_662_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1(lean_object* v_body_737_, lean_object* v_arg_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_expr_instantiate1(v_body_737_, v_arg_738_);
v___x_746_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_745_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4___boxed(lean_object* v_x_747_, lean_object* v_x_748_, lean_object* v_x_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(v_x_747_, v_x_748_, v_x_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___boxed(lean_object* v_upperBound_757_, lean_object* v_args_758_, lean_object* v_a_759_, lean_object* v_b_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v_upperBound_757_, v_args_758_, v_a_759_, v_b_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v_args_758_);
lean_dec(v_upperBound_757_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___boxed(lean_object* v_snd_768_, lean_object* v_args_769_, lean_object* v_a_770_, lean_object* v_____r_771_, lean_object* v_fty_772_, lean_object* v_j_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_snd_768_, v_args_769_, v_a_770_, v_____r_771_, v_fty_772_, v_j_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec(v_j_773_);
lean_dec(v_a_770_);
lean_dec_ref(v_args_769_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___boxed(lean_object* v_e_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_e_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec(v_a_782_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0(lean_object* v_00_u03b1_789_, lean_object* v_msg_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v_msg_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___boxed(lean_object* v_00_u03b1_797_, lean_object* v_msg_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0(v_00_u03b1_797_, v_msg_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1(lean_object* v_upperBound_805_, lean_object* v_args_806_, lean_object* v_inst_807_, lean_object* v_R_808_, lean_object* v_a_809_, lean_object* v_b_810_, lean_object* v_c_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v_upperBound_805_, v_args_806_, v_a_809_, v_b_810_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___boxed(lean_object* v_upperBound_819_, lean_object* v_args_820_, lean_object* v_inst_821_, lean_object* v_R_822_, lean_object* v_a_823_, lean_object* v_b_824_, lean_object* v_c_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1(v_upperBound_819_, v_args_820_, v_inst_821_, v_R_822_, v_a_823_, v_b_824_, v_c_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v_args_820_);
lean_dec(v_upperBound_819_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2(lean_object* v_00_u03b2_833_, lean_object* v_m_834_, lean_object* v_a_835_, lean_object* v_b_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v_m_834_, v_a_835_, v_b_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3(lean_object* v_00_u03b2_838_, lean_object* v_m_839_, lean_object* v_a_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v_m_839_, v_a_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___boxed(lean_object* v_00_u03b2_842_, lean_object* v_m_843_, lean_object* v_a_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3(v_00_u03b2_842_, v_m_843_, v_a_844_);
lean_dec_ref(v_a_844_);
lean_dec_ref(v_m_843_);
return v_res_845_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3(lean_object* v_00_u03b2_846_, lean_object* v_a_847_, lean_object* v_x_848_){
_start:
{
uint8_t v___x_849_; 
v___x_849_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_847_, v_x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___boxed(lean_object* v_00_u03b2_850_, lean_object* v_a_851_, lean_object* v_x_852_){
_start:
{
uint8_t v_res_853_; lean_object* v_r_854_; 
v_res_853_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3(v_00_u03b2_850_, v_a_851_, v_x_852_);
lean_dec(v_x_852_);
lean_dec_ref(v_a_851_);
v_r_854_ = lean_box(v_res_853_);
return v_r_854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4(lean_object* v_00_u03b2_855_, lean_object* v_data_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(v_data_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5(lean_object* v_00_u03b2_858_, lean_object* v_a_859_, lean_object* v_b_860_, lean_object* v_x_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(v_a_859_, v_b_860_, v_x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7(lean_object* v_00_u03b2_863_, lean_object* v_a_864_, lean_object* v_x_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(v_a_864_, v_x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___boxed(lean_object* v_00_u03b2_867_, lean_object* v_a_868_, lean_object* v_x_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7(v_00_u03b2_867_, v_a_868_, v_x_869_);
lean_dec(v_x_869_);
lean_dec_ref(v_a_868_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_871_, lean_object* v_i_872_, lean_object* v_source_873_, lean_object* v_target_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6___redArg(v_i_872_, v_source_873_, v_target_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_876_, lean_object* v_x_877_, lean_object* v_x_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9___redArg(v_x_877_, v_x_878_);
return v___x_879_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_880_ = lean_box(0);
v___x_881_ = lean_unsigned_to_nat(16u);
v___x_882_ = lean_mk_array(v___x_881_, v___x_880_);
return v___x_882_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_883_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0);
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v___x_883_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(lean_object* v_e_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1);
v___x_893_ = lean_st_mk_ref(v___x_892_);
v___x_894_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_e_886_, v___x_893_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_903_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_903_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_899_ = lean_st_ref_get(v___x_893_);
lean_dec(v___x_893_);
lean_dec(v___x_899_);
if (v_isShared_898_ == 0)
{
v___x_901_ = v___x_897_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_895_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
else
{
lean_dec(v___x_893_);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___boxed(lean_object* v_e_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(v_e_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
return v_res_910_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(lean_object* v_m_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_buckets_913_; lean_object* v___x_914_; uint64_t v___x_915_; uint64_t v___x_916_; uint64_t v___x_917_; uint64_t v_fold_918_; uint64_t v___x_919_; uint64_t v___x_920_; uint64_t v___x_921_; size_t v___x_922_; size_t v___x_923_; size_t v___x_924_; size_t v___x_925_; size_t v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v_buckets_913_ = lean_ctor_get(v_m_911_, 1);
v___x_914_ = lean_array_get_size(v_buckets_913_);
v___x_915_ = l_Lean_Expr_hash(v_a_912_);
v___x_916_ = 32ULL;
v___x_917_ = lean_uint64_shift_right(v___x_915_, v___x_916_);
v_fold_918_ = lean_uint64_xor(v___x_915_, v___x_917_);
v___x_919_ = 16ULL;
v___x_920_ = lean_uint64_shift_right(v_fold_918_, v___x_919_);
v___x_921_ = lean_uint64_xor(v_fold_918_, v___x_920_);
v___x_922_ = lean_uint64_to_usize(v___x_921_);
v___x_923_ = lean_usize_of_nat(v___x_914_);
v___x_924_ = ((size_t)1ULL);
v___x_925_ = lean_usize_sub(v___x_923_, v___x_924_);
v___x_926_ = lean_usize_land(v___x_922_, v___x_925_);
v___x_927_ = lean_array_uget_borrowed(v_buckets_913_, v___x_926_);
v___x_928_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_912_, v___x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg___boxed(lean_object* v_m_929_, lean_object* v_a_930_){
_start:
{
uint8_t v_res_931_; lean_object* v_r_932_; 
v_res_931_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_m_929_, v_a_930_);
lean_dec_ref(v_a_930_);
lean_dec_ref(v_m_929_);
v_r_932_ = lean_box(v_res_931_);
return v_r_932_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(lean_object* v_m_933_, lean_object* v_a_934_, lean_object* v_b_935_){
_start:
{
lean_object* v_size_936_; lean_object* v_buckets_937_; lean_object* v___x_938_; uint64_t v___x_939_; uint64_t v___x_940_; uint64_t v___x_941_; uint64_t v_fold_942_; uint64_t v___x_943_; uint64_t v___x_944_; uint64_t v___x_945_; size_t v___x_946_; size_t v___x_947_; size_t v___x_948_; size_t v___x_949_; size_t v___x_950_; lean_object* v_bkt_951_; uint8_t v___x_952_; 
v_size_936_ = lean_ctor_get(v_m_933_, 0);
v_buckets_937_ = lean_ctor_get(v_m_933_, 1);
v___x_938_ = lean_array_get_size(v_buckets_937_);
v___x_939_ = l_Lean_Expr_hash(v_a_934_);
v___x_940_ = 32ULL;
v___x_941_ = lean_uint64_shift_right(v___x_939_, v___x_940_);
v_fold_942_ = lean_uint64_xor(v___x_939_, v___x_941_);
v___x_943_ = 16ULL;
v___x_944_ = lean_uint64_shift_right(v_fold_942_, v___x_943_);
v___x_945_ = lean_uint64_xor(v_fold_942_, v___x_944_);
v___x_946_ = lean_uint64_to_usize(v___x_945_);
v___x_947_ = lean_usize_of_nat(v___x_938_);
v___x_948_ = ((size_t)1ULL);
v___x_949_ = lean_usize_sub(v___x_947_, v___x_948_);
v___x_950_ = lean_usize_land(v___x_946_, v___x_949_);
v_bkt_951_ = lean_array_uget_borrowed(v_buckets_937_, v___x_950_);
v___x_952_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_934_, v_bkt_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_973_; 
lean_inc_ref(v_buckets_937_);
lean_inc(v_size_936_);
v_isSharedCheck_973_ = !lean_is_exclusive(v_m_933_);
if (v_isSharedCheck_973_ == 0)
{
lean_object* v_unused_974_; lean_object* v_unused_975_; 
v_unused_974_ = lean_ctor_get(v_m_933_, 1);
lean_dec(v_unused_974_);
v_unused_975_ = lean_ctor_get(v_m_933_, 0);
lean_dec(v_unused_975_);
v___x_954_ = v_m_933_;
v_isShared_955_ = v_isSharedCheck_973_;
goto v_resetjp_953_;
}
else
{
lean_dec(v_m_933_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_973_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v_size_x27_957_; lean_object* v___x_958_; lean_object* v_buckets_x27_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; uint8_t v___x_965_; 
v___x_956_ = lean_unsigned_to_nat(1u);
v_size_x27_957_ = lean_nat_add(v_size_936_, v___x_956_);
lean_dec(v_size_936_);
lean_inc(v_bkt_951_);
v___x_958_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_958_, 0, v_a_934_);
lean_ctor_set(v___x_958_, 1, v_b_935_);
lean_ctor_set(v___x_958_, 2, v_bkt_951_);
v_buckets_x27_959_ = lean_array_uset(v_buckets_937_, v___x_950_, v___x_958_);
v___x_960_ = lean_unsigned_to_nat(4u);
v___x_961_ = lean_nat_mul(v_size_x27_957_, v___x_960_);
v___x_962_ = lean_unsigned_to_nat(3u);
v___x_963_ = lean_nat_div(v___x_961_, v___x_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_array_get_size(v_buckets_x27_959_);
v___x_965_ = lean_nat_dec_le(v___x_963_, v___x_964_);
lean_dec(v___x_963_);
if (v___x_965_ == 0)
{
lean_object* v_val_966_; lean_object* v___x_968_; 
v_val_966_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(v_buckets_x27_959_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v_val_966_);
lean_ctor_set(v___x_954_, 0, v_size_x27_957_);
v___x_968_ = v___x_954_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_size_x27_957_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_val_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
else
{
lean_object* v___x_971_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v_buckets_x27_959_);
lean_ctor_set(v___x_954_, 0, v_size_x27_957_);
v___x_971_ = v___x_954_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_size_x27_957_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_buckets_x27_959_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
else
{
lean_dec(v_b_935_);
lean_dec_ref(v_a_934_);
return v_m_933_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(lean_object* v_e_981_, uint8_t v_omitTopForall_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
switch(lean_obj_tag(v_e_981_))
{
case 4:
{
lean_object* v_declName_989_; lean_object* v___x_990_; lean_object* v_seen_991_; lean_object* v_consts_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1019_; 
v_declName_989_ = lean_ctor_get(v_e_981_, 0);
lean_inc(v_declName_989_);
lean_dec_ref_known(v_e_981_, 2);
v___x_990_ = lean_st_ref_take(v_a_983_);
v_seen_991_ = lean_ctor_get(v___x_990_, 0);
v_consts_992_ = lean_ctor_get(v___x_990_, 1);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_994_ = v___x_990_;
v_isShared_995_ = v_isSharedCheck_1019_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_consts_992_);
lean_inc(v_seen_991_);
lean_dec(v___x_990_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1019_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_996_; lean_object* v___x_998_; 
lean_inc(v_declName_989_);
v___x_996_ = l_Lean_NameSet_insert(v_consts_992_, v_declName_989_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 1, v___x_996_);
v___x_998_ = v___x_994_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_seen_991_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v___x_996_);
v___x_998_ = v_reuseFailAlloc_1018_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_st_ref_put(v_a_983_, v___x_998_);
v___x_1000_ = l_Lean_Name_eraseMacroScopes(v_declName_989_);
lean_dec(v_declName_989_);
if (lean_obj_tag(v___x_1000_) == 1)
{
lean_object* v_str_1001_; lean_object* v___x_1002_; uint32_t v___x_1003_; uint8_t v___y_1005_; uint32_t v___x_1012_; uint8_t v___x_1013_; 
v_str_1001_ = lean_ctor_get(v___x_1000_, 1);
lean_inc_ref(v_str_1001_);
lean_dec_ref_known(v___x_1000_, 2);
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = lean_string_utf8_get(v_str_1001_, v___x_1002_);
v___x_1012_ = 97;
v___x_1013_ = lean_uint32_dec_le(v___x_1012_, v___x_1003_);
if (v___x_1013_ == 0)
{
v___y_1005_ = v___x_1013_;
goto v___jp_1004_;
}
else
{
uint32_t v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = 122;
v___x_1015_ = lean_uint32_dec_le(v___x_1003_, v___x_1014_);
v___y_1005_ = v___x_1015_;
goto v___jp_1004_;
}
v___jp_1004_:
{
if (v___y_1005_ == 0)
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = lean_string_utf8_set(v_str_1001_, v___x_1002_, v___x_1003_);
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
return v___x_1007_;
}
else
{
uint32_t v___x_1008_; uint32_t v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1008_ = 4294967264;
v___x_1009_ = lean_uint32_add(v___x_1003_, v___x_1008_);
v___x_1010_ = lean_string_utf8_set(v_str_1001_, v___x_1002_, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
return v___x_1011_;
}
}
}
else
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec(v___x_1000_);
v___x_1016_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
return v___x_1017_;
}
}
}
}
case 5:
{
lean_object* v_fn_1020_; lean_object* v_arg_1021_; uint8_t v___x_1022_; lean_object* v___x_1023_; lean_object* v_a_1024_; lean_object* v___x_1025_; lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1034_; 
v_fn_1020_ = lean_ctor_get(v_e_981_, 0);
lean_inc_ref(v_fn_1020_);
v_arg_1021_ = lean_ctor_get(v_e_981_, 1);
lean_inc_ref(v_arg_1021_);
lean_dec_ref_known(v_e_981_, 2);
v___x_1022_ = 0;
v___x_1023_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_fn_1020_, v___x_1022_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref(v___x_1023_);
v___x_1025_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_arg_1021_, v___x_1022_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1030_ = lean_string_append(v_a_1024_, v_a_1026_);
lean_dec(v_a_1026_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1030_);
v___x_1032_ = v___x_1028_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
case 7:
{
lean_object* v_binderType_1035_; lean_object* v_body_1036_; uint8_t v___x_1037_; lean_object* v___x_1038_; lean_object* v_a_1039_; 
v_binderType_1035_ = lean_ctor_get(v_e_981_, 1);
lean_inc_ref(v_binderType_1035_);
v_body_1036_ = lean_ctor_get(v_e_981_, 2);
lean_inc_ref(v_body_1036_);
lean_dec_ref_known(v_e_981_, 3);
v___x_1037_ = 0;
v___x_1038_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_binderType_1035_, v___x_1037_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1039_);
lean_dec_ref(v___x_1038_);
if (v_omitTopForall_982_ == 0)
{
goto v___jp_1040_;
}
else
{
lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1054_ = lean_string_dec_eq(v_a_1039_, v___x_1053_);
if (v___x_1054_ == 0)
{
goto v___jp_1040_;
}
else
{
lean_object* v___x_1055_; 
lean_dec(v_a_1039_);
v___x_1055_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_body_1036_, v_omitTopForall_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
return v___x_1055_;
}
}
v___jp_1040_:
{
lean_object* v___x_1041_; lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1052_; 
v___x_1041_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_body_1036_, v___x_1037_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1044_ = v___x_1041_;
v_isShared_1045_ = v_isSharedCheck_1052_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1052_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1046_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0));
v___x_1047_ = lean_string_append(v___x_1046_, v_a_1039_);
lean_dec(v_a_1039_);
v___x_1048_ = lean_string_append(v___x_1047_, v_a_1042_);
lean_dec(v_a_1042_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1048_);
v___x_1050_ = v___x_1044_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
case 3:
{
lean_object* v_u_1056_; 
v_u_1056_ = lean_ctor_get(v_e_981_, 0);
lean_inc(v_u_1056_);
lean_dec_ref_known(v_e_981_, 1);
switch(lean_obj_tag(v_u_1056_))
{
case 0:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__1));
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
return v___x_1058_;
}
case 1:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
lean_dec_ref_known(v_u_1056_, 1);
v___x_1059_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__2));
v___x_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
return v___x_1060_;
}
default: 
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
lean_dec(v_u_1056_);
v___x_1061_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__3));
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
return v___x_1062_;
}
}
}
default: 
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
lean_dec_ref(v_e_981_);
v___x_1063_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
return v___x_1064_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(lean_object* v_e_1065_, uint8_t v_omitTopForall_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v___x_1073_; lean_object* v_seen_1074_; uint8_t v___x_1075_; 
v___x_1073_ = lean_st_ref_get(v_a_1067_);
v_seen_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc_ref(v_seen_1074_);
lean_dec(v___x_1073_);
v___x_1075_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_seen_1074_, v_e_1065_);
lean_dec_ref(v_seen_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1097_; 
lean_inc_ref(v_e_1065_);
v___x_1076_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(v_e_1065_, v_omitTopForall_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1097_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1097_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1081_; lean_object* v_seen_1082_; lean_object* v_consts_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1096_; 
v___x_1081_ = lean_st_ref_take(v_a_1067_);
v_seen_1082_ = lean_ctor_get(v___x_1081_, 0);
v_consts_1083_ = lean_ctor_get(v___x_1081_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1085_ = v___x_1081_;
v_isShared_1086_ = v_isSharedCheck_1096_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_consts_1083_);
lean_inc(v_seen_1082_);
lean_dec(v___x_1081_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1096_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1087_ = lean_box(0);
v___x_1088_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(v_seen_1082_, v_e_1065_, v___x_1087_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1088_);
v___x_1090_ = v___x_1085_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_consts_1083_);
v___x_1090_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1091_ = lean_st_ref_put(v_a_1067_, v___x_1090_);
if (v_isShared_1080_ == 0)
{
v___x_1093_ = v___x_1079_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1077_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_dec_ref(v_e_1065_);
v___x_1098_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
return v___x_1099_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___boxed(lean_object* v_e_1100_, lean_object* v_omitTopForall_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
uint8_t v_omitTopForall_boxed_1108_; lean_object* v_res_1109_; 
v_omitTopForall_boxed_1108_ = lean_unbox(v_omitTopForall_1101_);
v_res_1109_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_e_1100_, v_omitTopForall_boxed_1108_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___boxed(lean_object* v_e_1110_, lean_object* v_omitTopForall_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
uint8_t v_omitTopForall_boxed_1118_; lean_object* v_res_1119_; 
v_omitTopForall_boxed_1118_ = lean_unbox(v_omitTopForall_1111_);
v_res_1119_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(v_e_1110_, v_omitTopForall_boxed_1118_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1112_);
return v_res_1119_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0(lean_object* v_00_u03b2_1120_, lean_object* v_m_1121_, lean_object* v_a_1122_){
_start:
{
uint8_t v___x_1123_; 
v___x_1123_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_m_1121_, v_a_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___boxed(lean_object* v_00_u03b2_1124_, lean_object* v_m_1125_, lean_object* v_a_1126_){
_start:
{
uint8_t v_res_1127_; lean_object* v_r_1128_; 
v_res_1127_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0(v_00_u03b2_1124_, v_m_1125_, v_a_1126_);
lean_dec_ref(v_a_1126_);
lean_dec_ref(v_m_1125_);
v_r_1128_ = lean_box(v_res_1127_);
return v_r_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1(lean_object* v_00_u03b2_1129_, lean_object* v_m_1130_, lean_object* v_a_1131_, lean_object* v_b_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(v_m_1130_, v_a_1131_, v_b_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__3_splitter___redArg(lean_object* v_e_1134_, lean_object* v_h__1_1135_, lean_object* v_h__2_1136_, lean_object* v_h__3_1137_, lean_object* v_h__4_1138_, lean_object* v_h__5_1139_, lean_object* v_h__6_1140_, lean_object* v_h__7_1141_){
_start:
{
switch(lean_obj_tag(v_e_1134_))
{
case 4:
{
lean_object* v_declName_1142_; lean_object* v_us_1143_; lean_object* v___x_1144_; 
lean_dec(v_h__7_1141_);
lean_dec(v_h__6_1140_);
lean_dec(v_h__5_1139_);
lean_dec(v_h__4_1138_);
lean_dec(v_h__3_1137_);
lean_dec(v_h__2_1136_);
v_declName_1142_ = lean_ctor_get(v_e_1134_, 0);
lean_inc(v_declName_1142_);
v_us_1143_ = lean_ctor_get(v_e_1134_, 1);
lean_inc(v_us_1143_);
lean_dec_ref_known(v_e_1134_, 2);
v___x_1144_ = lean_apply_2(v_h__1_1135_, v_declName_1142_, v_us_1143_);
return v___x_1144_;
}
case 5:
{
lean_object* v_fn_1145_; lean_object* v_arg_1146_; lean_object* v___x_1147_; 
lean_dec(v_h__7_1141_);
lean_dec(v_h__6_1140_);
lean_dec(v_h__5_1139_);
lean_dec(v_h__4_1138_);
lean_dec(v_h__3_1137_);
lean_dec(v_h__1_1135_);
v_fn_1145_ = lean_ctor_get(v_e_1134_, 0);
lean_inc_ref(v_fn_1145_);
v_arg_1146_ = lean_ctor_get(v_e_1134_, 1);
lean_inc_ref(v_arg_1146_);
lean_dec_ref_known(v_e_1134_, 2);
v___x_1147_ = lean_apply_2(v_h__2_1136_, v_fn_1145_, v_arg_1146_);
return v___x_1147_;
}
case 7:
{
lean_object* v_binderName_1148_; lean_object* v_binderType_1149_; lean_object* v_body_1150_; uint8_t v_binderInfo_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_dec(v_h__7_1141_);
lean_dec(v_h__6_1140_);
lean_dec(v_h__5_1139_);
lean_dec(v_h__4_1138_);
lean_dec(v_h__2_1136_);
lean_dec(v_h__1_1135_);
v_binderName_1148_ = lean_ctor_get(v_e_1134_, 0);
lean_inc(v_binderName_1148_);
v_binderType_1149_ = lean_ctor_get(v_e_1134_, 1);
lean_inc_ref(v_binderType_1149_);
v_body_1150_ = lean_ctor_get(v_e_1134_, 2);
lean_inc_ref(v_body_1150_);
v_binderInfo_1151_ = lean_ctor_get_uint8(v_e_1134_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1134_, 3);
v___x_1152_ = lean_box(v_binderInfo_1151_);
v___x_1153_ = lean_apply_4(v_h__3_1137_, v_binderName_1148_, v_binderType_1149_, v_body_1150_, v___x_1152_);
return v___x_1153_;
}
case 3:
{
lean_object* v_u_1154_; 
lean_dec(v_h__7_1141_);
lean_dec(v_h__3_1137_);
lean_dec(v_h__2_1136_);
lean_dec(v_h__1_1135_);
v_u_1154_ = lean_ctor_get(v_e_1134_, 0);
lean_inc(v_u_1154_);
lean_dec_ref_known(v_e_1134_, 1);
switch(lean_obj_tag(v_u_1154_))
{
case 0:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
lean_dec(v_h__6_1140_);
lean_dec(v_h__5_1139_);
v___x_1155_ = lean_box(0);
v___x_1156_ = lean_apply_1(v_h__4_1138_, v___x_1155_);
return v___x_1156_;
}
case 1:
{
lean_object* v_a_1157_; lean_object* v___x_1158_; 
lean_dec(v_h__6_1140_);
lean_dec(v_h__4_1138_);
v_a_1157_ = lean_ctor_get(v_u_1154_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v_u_1154_, 1);
v___x_1158_ = lean_apply_1(v_h__5_1139_, v_a_1157_);
return v___x_1158_;
}
default: 
{
lean_object* v___x_1159_; 
lean_dec(v_h__5_1139_);
lean_dec(v_h__4_1138_);
v___x_1159_ = lean_apply_3(v_h__6_1140_, v_u_1154_, lean_box(0), lean_box(0));
return v___x_1159_;
}
}
}
default: 
{
lean_object* v___x_1160_; 
lean_dec(v_h__6_1140_);
lean_dec(v_h__5_1139_);
lean_dec(v_h__4_1138_);
lean_dec(v_h__3_1137_);
lean_dec(v_h__2_1136_);
lean_dec(v_h__1_1135_);
v___x_1160_ = lean_apply_7(v_h__7_1141_, v_e_1134_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1160_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__3_splitter(lean_object* v_motive_1161_, lean_object* v_e_1162_, lean_object* v_h__1_1163_, lean_object* v_h__2_1164_, lean_object* v_h__3_1165_, lean_object* v_h__4_1166_, lean_object* v_h__5_1167_, lean_object* v_h__6_1168_, lean_object* v_h__7_1169_){
_start:
{
switch(lean_obj_tag(v_e_1162_))
{
case 4:
{
lean_object* v_declName_1170_; lean_object* v_us_1171_; lean_object* v___x_1172_; 
lean_dec(v_h__7_1169_);
lean_dec(v_h__6_1168_);
lean_dec(v_h__5_1167_);
lean_dec(v_h__4_1166_);
lean_dec(v_h__3_1165_);
lean_dec(v_h__2_1164_);
v_declName_1170_ = lean_ctor_get(v_e_1162_, 0);
lean_inc(v_declName_1170_);
v_us_1171_ = lean_ctor_get(v_e_1162_, 1);
lean_inc(v_us_1171_);
lean_dec_ref_known(v_e_1162_, 2);
v___x_1172_ = lean_apply_2(v_h__1_1163_, v_declName_1170_, v_us_1171_);
return v___x_1172_;
}
case 5:
{
lean_object* v_fn_1173_; lean_object* v_arg_1174_; lean_object* v___x_1175_; 
lean_dec(v_h__7_1169_);
lean_dec(v_h__6_1168_);
lean_dec(v_h__5_1167_);
lean_dec(v_h__4_1166_);
lean_dec(v_h__3_1165_);
lean_dec(v_h__1_1163_);
v_fn_1173_ = lean_ctor_get(v_e_1162_, 0);
lean_inc_ref(v_fn_1173_);
v_arg_1174_ = lean_ctor_get(v_e_1162_, 1);
lean_inc_ref(v_arg_1174_);
lean_dec_ref_known(v_e_1162_, 2);
v___x_1175_ = lean_apply_2(v_h__2_1164_, v_fn_1173_, v_arg_1174_);
return v___x_1175_;
}
case 7:
{
lean_object* v_binderName_1176_; lean_object* v_binderType_1177_; lean_object* v_body_1178_; uint8_t v_binderInfo_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
lean_dec(v_h__7_1169_);
lean_dec(v_h__6_1168_);
lean_dec(v_h__5_1167_);
lean_dec(v_h__4_1166_);
lean_dec(v_h__2_1164_);
lean_dec(v_h__1_1163_);
v_binderName_1176_ = lean_ctor_get(v_e_1162_, 0);
lean_inc(v_binderName_1176_);
v_binderType_1177_ = lean_ctor_get(v_e_1162_, 1);
lean_inc_ref(v_binderType_1177_);
v_body_1178_ = lean_ctor_get(v_e_1162_, 2);
lean_inc_ref(v_body_1178_);
v_binderInfo_1179_ = lean_ctor_get_uint8(v_e_1162_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1162_, 3);
v___x_1180_ = lean_box(v_binderInfo_1179_);
v___x_1181_ = lean_apply_4(v_h__3_1165_, v_binderName_1176_, v_binderType_1177_, v_body_1178_, v___x_1180_);
return v___x_1181_;
}
case 3:
{
lean_object* v_u_1182_; 
lean_dec(v_h__7_1169_);
lean_dec(v_h__3_1165_);
lean_dec(v_h__2_1164_);
lean_dec(v_h__1_1163_);
v_u_1182_ = lean_ctor_get(v_e_1162_, 0);
lean_inc(v_u_1182_);
lean_dec_ref_known(v_e_1162_, 1);
switch(lean_obj_tag(v_u_1182_))
{
case 0:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
lean_dec(v_h__6_1168_);
lean_dec(v_h__5_1167_);
v___x_1183_ = lean_box(0);
v___x_1184_ = lean_apply_1(v_h__4_1166_, v___x_1183_);
return v___x_1184_;
}
case 1:
{
lean_object* v_a_1185_; lean_object* v___x_1186_; 
lean_dec(v_h__6_1168_);
lean_dec(v_h__4_1166_);
v_a_1185_ = lean_ctor_get(v_u_1182_, 0);
lean_inc(v_a_1185_);
lean_dec_ref_known(v_u_1182_, 1);
v___x_1186_ = lean_apply_1(v_h__5_1167_, v_a_1185_);
return v___x_1186_;
}
default: 
{
lean_object* v___x_1187_; 
lean_dec(v_h__5_1167_);
lean_dec(v_h__4_1166_);
v___x_1187_ = lean_apply_3(v_h__6_1168_, v_u_1182_, lean_box(0), lean_box(0));
return v___x_1187_;
}
}
}
default: 
{
lean_object* v___x_1188_; 
lean_dec(v_h__6_1168_);
lean_dec(v_h__5_1167_);
lean_dec(v_h__4_1166_);
lean_dec(v_h__3_1165_);
lean_dec(v_h__2_1164_);
lean_dec(v_h__1_1163_);
v___x_1188_ = lean_apply_7(v_h__7_1169_, v_e_1162_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1188_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__1_splitter___redArg(lean_object* v_x_1189_, lean_object* v_h__1_1190_, lean_object* v_h__2_1191_){
_start:
{
if (lean_obj_tag(v_x_1189_) == 1)
{
lean_object* v_pre_1192_; lean_object* v_str_1193_; lean_object* v___x_1194_; 
lean_dec(v_h__2_1191_);
v_pre_1192_ = lean_ctor_get(v_x_1189_, 0);
lean_inc(v_pre_1192_);
v_str_1193_ = lean_ctor_get(v_x_1189_, 1);
lean_inc_ref(v_str_1193_);
lean_dec_ref_known(v_x_1189_, 2);
v___x_1194_ = lean_apply_2(v_h__1_1190_, v_pre_1192_, v_str_1193_);
return v___x_1194_;
}
else
{
lean_object* v___x_1195_; 
lean_dec(v_h__1_1190_);
v___x_1195_ = lean_apply_2(v_h__2_1191_, v_x_1189_, lean_box(0));
return v___x_1195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__1_splitter(lean_object* v_motive_1196_, lean_object* v_x_1197_, lean_object* v_h__1_1198_, lean_object* v_h__2_1199_){
_start:
{
if (lean_obj_tag(v_x_1197_) == 1)
{
lean_object* v_pre_1200_; lean_object* v_str_1201_; lean_object* v___x_1202_; 
lean_dec(v_h__2_1199_);
v_pre_1200_ = lean_ctor_get(v_x_1197_, 0);
lean_inc(v_pre_1200_);
v_str_1201_ = lean_ctor_get(v_x_1197_, 1);
lean_inc_ref(v_str_1201_);
lean_dec_ref_known(v_x_1197_, 2);
v___x_1202_ = lean_apply_2(v_h__1_1198_, v_pre_1200_, v_str_1201_);
return v___x_1202_;
}
else
{
lean_object* v___x_1203_; 
lean_dec(v_h__1_1198_);
v___x_1203_ = lean_apply_2(v_h__2_1199_, v_x_1197_, lean_box(0));
return v___x_1203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore(lean_object* v_e_1204_, uint8_t v_omitTopForall_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_e_1204_, v_omitTopForall_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore___boxed(lean_object* v_e_1213_, lean_object* v_omitTopForall_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
uint8_t v_omitTopForall_boxed_1221_; lean_object* v_res_1222_; 
v_omitTopForall_boxed_1221_ = lean_unbox(v_omitTopForall_1214_);
v_res_1222_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore(v_e_1213_, v_omitTopForall_boxed_1221_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(lean_object* v_e_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
if (lean_obj_tag(v_e_1224_) == 7)
{
lean_object* v_binderType_1231_; lean_object* v_body_1232_; lean_object* v___x_1233_; 
v_binderType_1231_ = lean_ctor_get(v_e_1224_, 1);
lean_inc_ref(v_binderType_1231_);
v_body_1232_ = lean_ctor_get(v_e_1224_, 2);
lean_inc_ref(v_body_1232_);
lean_dec_ref_known(v_e_1224_, 3);
v___x_1233_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(v_body_1232_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v_fst_1235_; lean_object* v_snd_1236_; uint8_t v___x_1237_; lean_object* v___x_1238_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1234_);
lean_dec_ref_known(v___x_1233_, 1);
v_fst_1235_ = lean_ctor_get(v_a_1234_, 0);
v_snd_1236_ = lean_ctor_get(v_a_1234_, 1);
v___x_1237_ = 1;
v___x_1238_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_binderType_1231_, v___x_1237_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1263_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1241_ = v___x_1238_;
v_isShared_1242_ = v_isSharedCheck_1263_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1263_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1243_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1244_ = lean_string_dec_eq(v_a_1239_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1257_; 
lean_inc(v_snd_1236_);
lean_inc(v_fst_1235_);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_a_1234_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; lean_object* v_unused_1259_; 
v_unused_1258_ = lean_ctor_get(v_a_1234_, 1);
lean_dec(v_unused_1258_);
v_unused_1259_ = lean_ctor_get(v_a_1234_, 0);
lean_dec(v_unused_1259_);
v___x_1246_ = v_a_1234_;
v_isShared_1247_ = v_isSharedCheck_1257_;
goto v_resetjp_1245_;
}
else
{
lean_dec(v_a_1234_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1257_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1248_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit___closed__0));
v___x_1249_ = lean_string_append(v___x_1248_, v_a_1239_);
lean_dec(v_a_1239_);
v___x_1250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
lean_ctor_set(v___x_1250_, 1, v_fst_1235_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1250_);
v___x_1252_ = v___x_1246_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_snd_1236_);
v___x_1252_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1254_; 
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 0, v___x_1252_);
v___x_1254_ = v___x_1241_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
else
{
lean_object* v___x_1261_; 
lean_dec(v_a_1239_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 0, v_a_1234_);
v___x_1261_ = v___x_1241_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1234_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v_a_1234_);
v_a_1264_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1238_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1238_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_1231_);
return v___x_1233_;
}
}
else
{
uint8_t v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = 0;
v___x_1273_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_e_1224_, v___x_1272_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1283_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1283_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1283_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1278_ = lean_box(0);
v___x_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
lean_ctor_set(v___x_1279_, 1, v_a_1274_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1279_);
v___x_1281_ = v___x_1276_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
v_a_1284_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1273_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1273_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit___boxed(lean_object* v_e_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(v_e_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(lean_object* v_x_1300_, lean_object* v_x_1301_){
_start:
{
if (lean_obj_tag(v_x_1301_) == 0)
{
return v_x_1300_;
}
else
{
lean_object* v_head_1302_; lean_object* v_tail_1303_; lean_object* v___x_1304_; 
v_head_1302_ = lean_ctor_get(v_x_1301_, 0);
v_tail_1303_ = lean_ctor_get(v_x_1301_, 1);
v___x_1304_ = lean_string_append(v_x_1300_, v_head_1302_);
v_x_1300_ = v___x_1304_;
v_x_1301_ = v_tail_1303_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0___boxed(lean_object* v_x_1306_, lean_object* v_x_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(v_x_1306_, v_x_1307_);
lean_dec(v_x_1307_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(lean_object* v_e_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(v_e_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1329_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1329_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1329_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v_fst_1321_; lean_object* v_snd_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
v_fst_1321_ = lean_ctor_get(v_a_1317_, 0);
lean_inc(v_fst_1321_);
v_snd_1322_ = lean_ctor_get(v_a_1317_, 1);
lean_inc(v_snd_1322_);
lean_dec(v_a_1317_);
v___x_1323_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1324_ = l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(v___x_1323_, v_fst_1321_);
lean_dec(v_fst_1321_);
v___x_1325_ = lean_string_append(v_snd_1322_, v___x_1324_);
lean_dec_ref(v___x_1324_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v___x_1325_);
v___x_1327_ = v___x_1319_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
v_a_1330_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1316_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1316_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux___boxed(lean_object* v_e_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(v_e_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_);
lean_dec(v_a_1343_);
lean_dec_ref(v_a_1342_);
lean_dec(v_a_1341_);
lean_dec_ref(v_a_1340_);
lean_dec(v_a_1339_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(lean_object* v_ns_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
switch(lean_obj_tag(v_ns_1346_))
{
case 0:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = lean_box(0);
v___x_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
return v___x_1351_;
}
case 1:
{
lean_object* v_pre_1352_; lean_object* v___x_1353_; lean_object* v_env_1354_; uint8_t v___x_1355_; uint8_t v___x_1356_; 
v_pre_1352_ = lean_ctor_get(v_ns_1346_, 0);
lean_inc(v_pre_1352_);
v___x_1353_ = lean_st_ref_get(v_a_1348_);
v_env_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc_ref(v_env_1354_);
lean_dec(v___x_1353_);
v___x_1355_ = 1;
lean_inc_ref(v_ns_1346_);
v___x_1356_ = l_Lean_Environment_contains(v_env_1354_, v_ns_1346_, v___x_1355_);
if (v___x_1356_ == 0)
{
lean_dec_ref_known(v_ns_1346_, 2);
v_ns_1346_ = v_pre_1352_;
goto _start;
}
else
{
lean_object* v___x_1358_; lean_object* v_seen_1359_; lean_object* v_consts_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1374_; 
v___x_1358_ = lean_st_ref_take(v_a_1347_);
v_seen_1359_ = lean_ctor_get(v___x_1358_, 0);
v_consts_1360_ = lean_ctor_get(v___x_1358_, 1);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1362_ = v___x_1358_;
v_isShared_1363_ = v_isSharedCheck_1374_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_consts_1360_);
lean_inc(v_seen_1359_);
lean_dec(v___x_1358_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1374_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1364_ = lean_box(0);
lean_inc_ref(v_ns_1346_);
v___x_1365_ = l_Lean_Expr_const___override(v_ns_1346_, v___x_1364_);
v___x_1366_ = lean_box(0);
v___x_1367_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(v_seen_1359_, v___x_1365_, v___x_1366_);
v___x_1368_ = l_Lean_NameSet_insert(v_consts_1360_, v_ns_1346_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 1, v___x_1368_);
lean_ctor_set(v___x_1362_, 0, v___x_1367_);
v___x_1370_ = v___x_1362_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_st_ref_put(v_a_1347_, v___x_1370_);
v_ns_1346_ = v_pre_1352_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_pre_1375_; 
v_pre_1375_ = lean_ctor_get(v_ns_1346_, 0);
lean_inc(v_pre_1375_);
lean_dec_ref_known(v_ns_1346_, 2);
v_ns_1346_ = v_pre_1375_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg___boxed(lean_object* v_ns_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(v_ns_1377_, v_a_1378_, v_a_1379_);
lean_dec(v_a_1379_);
lean_dec(v_a_1378_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace(lean_object* v_ns_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(v_ns_1382_, v_a_1383_, v_a_1387_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___boxed(lean_object* v_ns_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace(v_ns_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(lean_object* v_e_1398_, lean_object* v___y_1399_){
_start:
{
uint8_t v___x_1401_; 
v___x_1401_ = l_Lean_Expr_hasMVar(v_e_1398_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1402_, 0, v_e_1398_);
return v___x_1402_;
}
else
{
lean_object* v___x_1403_; lean_object* v_mctx_1404_; lean_object* v___x_1405_; lean_object* v_fst_1406_; lean_object* v_snd_1407_; lean_object* v___x_1408_; lean_object* v_cache_1409_; lean_object* v_zetaDeltaFVarIds_1410_; lean_object* v_postponed_1411_; lean_object* v_diag_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1421_; 
v___x_1403_ = lean_st_ref_get(v___y_1399_);
v_mctx_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc_ref(v_mctx_1404_);
lean_dec(v___x_1403_);
v___x_1405_ = l_Lean_instantiateMVarsCore(v_mctx_1404_, v_e_1398_);
v_fst_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_fst_1406_);
v_snd_1407_ = lean_ctor_get(v___x_1405_, 1);
lean_inc(v_snd_1407_);
lean_dec_ref(v___x_1405_);
v___x_1408_ = lean_st_ref_take(v___y_1399_);
v_cache_1409_ = lean_ctor_get(v___x_1408_, 1);
v_zetaDeltaFVarIds_1410_ = lean_ctor_get(v___x_1408_, 2);
v_postponed_1411_ = lean_ctor_get(v___x_1408_, 3);
v_diag_1412_ = lean_ctor_get(v___x_1408_, 4);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; 
v_unused_1422_ = lean_ctor_get(v___x_1408_, 0);
lean_dec(v_unused_1422_);
v___x_1414_ = v___x_1408_;
v_isShared_1415_ = v_isSharedCheck_1421_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_diag_1412_);
lean_inc(v_postponed_1411_);
lean_inc(v_zetaDeltaFVarIds_1410_);
lean_inc(v_cache_1409_);
lean_dec(v___x_1408_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1421_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v_snd_1407_);
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_snd_1407_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_cache_1409_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v_zetaDeltaFVarIds_1410_);
lean_ctor_set(v_reuseFailAlloc_1420_, 3, v_postponed_1411_);
lean_ctor_set(v_reuseFailAlloc_1420_, 4, v_diag_1412_);
v___x_1417_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = lean_st_ref_put(v___y_1399_, v___x_1417_);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v_fst_1406_);
return v___x_1419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg___boxed(lean_object* v_e_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_1423_, v___y_1424_);
lean_dec(v___y_1424_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0(lean_object* v_e_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_1427_, v___y_1430_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___boxed(lean_object* v_e_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0(v_e_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(lean_object* v_e_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v___x_1450_; lean_object* v_toCold_1451_; lean_object* v_a_1452_; lean_object* v_currNamespace_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1450_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_1443_, v_a_1446_);
v_toCold_1451_ = lean_ctor_get(v_a_1447_, 0);
v_a_1452_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1452_);
lean_dec_ref(v___x_1450_);
v_currNamespace_1453_ = lean_ctor_get(v_toCold_1451_, 4);
lean_inc(v_currNamespace_1453_);
v___x_1454_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(v_currNamespace_1453_, v_a_1444_, v_a_1448_);
lean_dec_ref(v___x_1454_);
v___x_1455_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(v_a_1452_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1457_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref_known(v___x_1455_, 1);
v___x_1457_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(v_a_1456_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
return v___x_1457_;
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
v_a_1458_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1455_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1455_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName___boxed(lean_object* v_e_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(v_e_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
lean_dec(v_a_1467_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(lean_object* v_x_1475_){
_start:
{
switch(lean_obj_tag(v_x_1475_))
{
case 0:
{
lean_object* v___x_1476_; 
v___x_1476_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
return v___x_1476_;
}
case 1:
{
lean_object* v_pre_1477_; lean_object* v_str_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; uint32_t v___x_1483_; uint8_t v___y_1485_; uint32_t v___x_1492_; uint8_t v___x_1493_; 
v_pre_1477_ = lean_ctor_get(v_x_1475_, 0);
lean_inc(v_pre_1477_);
v_str_1478_ = lean_ctor_get(v_x_1475_, 1);
lean_inc_ref(v_str_1478_);
lean_dec_ref_known(v_x_1475_, 2);
v___x_1479_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(v_pre_1477_);
v___x_1480_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix___closed__0));
v___x_1481_ = lean_string_append(v___x_1479_, v___x_1480_);
v___x_1482_ = lean_unsigned_to_nat(0u);
v___x_1483_ = lean_string_utf8_get(v_str_1478_, v___x_1482_);
v___x_1492_ = 65;
v___x_1493_ = lean_uint32_dec_le(v___x_1492_, v___x_1483_);
if (v___x_1493_ == 0)
{
v___y_1485_ = v___x_1493_;
goto v___jp_1484_;
}
else
{
uint32_t v___x_1494_; uint8_t v___x_1495_; 
v___x_1494_ = 90;
v___x_1495_ = lean_uint32_dec_le(v___x_1483_, v___x_1494_);
v___y_1485_ = v___x_1495_;
goto v___jp_1484_;
}
v___jp_1484_:
{
if (v___y_1485_ == 0)
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = lean_string_utf8_set(v_str_1478_, v___x_1482_, v___x_1483_);
v___x_1487_ = lean_string_append(v___x_1481_, v___x_1486_);
lean_dec_ref(v___x_1486_);
return v___x_1487_;
}
else
{
uint32_t v___x_1488_; uint32_t v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1488_ = 32;
v___x_1489_ = lean_uint32_add(v___x_1483_, v___x_1488_);
v___x_1490_ = lean_string_utf8_set(v_str_1478_, v___x_1482_, v___x_1489_);
v___x_1491_ = lean_string_append(v___x_1481_, v___x_1490_);
lean_dec_ref(v___x_1490_);
return v___x_1491_;
}
}
}
default: 
{
lean_object* v_pre_1496_; 
v_pre_1496_ = lean_ctor_get(v_x_1475_, 0);
lean_inc(v_pre_1496_);
lean_dec_ref_known(v_x_1475_, 2);
v_x_1475_ = v_pre_1496_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(lean_object* v___y_1498_){
_start:
{
lean_object* v___x_1500_; lean_object* v_env_1501_; lean_object* v___x_1502_; lean_object* v_mainModule_1503_; lean_object* v___x_1504_; 
v___x_1500_ = lean_st_ref_get(v___y_1498_);
v_env_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc_ref(v_env_1501_);
lean_dec(v___x_1500_);
v___x_1502_ = l_Lean_Environment_header(v_env_1501_);
lean_dec_ref(v_env_1501_);
v_mainModule_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_mainModule_1503_);
lean_dec_ref(v___x_1502_);
v___x_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1504_, 0, v_mainModule_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg___boxed(lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v___y_1505_);
lean_dec(v___y_1505_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1(lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v___y_1511_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___boxed(lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1(v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
return v_res_1519_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(lean_object* v_x_1520_, lean_object* v_x_1521_){
_start:
{
if (lean_obj_tag(v_x_1520_) == 0)
{
if (lean_obj_tag(v_x_1521_) == 0)
{
uint8_t v___x_1522_; 
v___x_1522_ = 1;
return v___x_1522_;
}
else
{
uint8_t v___x_1523_; 
v___x_1523_ = 0;
return v___x_1523_;
}
}
else
{
if (lean_obj_tag(v_x_1521_) == 0)
{
uint8_t v___x_1524_; 
v___x_1524_ = 0;
return v___x_1524_;
}
else
{
lean_object* v_val_1525_; lean_object* v_val_1526_; uint8_t v___x_1527_; 
v_val_1525_ = lean_ctor_get(v_x_1520_, 0);
v_val_1526_ = lean_ctor_get(v_x_1521_, 0);
v___x_1527_ = lean_name_eq(v_val_1525_, v_val_1526_);
return v___x_1527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2___boxed(lean_object* v_x_1528_, lean_object* v_x_1529_){
_start:
{
uint8_t v_res_1530_; lean_object* v_r_1531_; 
v_res_1530_ = l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(v_x_1528_, v_x_1529_);
lean_dec(v_x_1529_);
lean_dec(v_x_1528_);
v_r_1531_ = lean_box(v_res_1530_);
return v_r_1531_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0(lean_object* v_e_1532_){
_start:
{
if (lean_obj_tag(v_e_1532_) == 4)
{
lean_object* v_declName_1533_; uint8_t v___x_1534_; 
v_declName_1533_ = lean_ctor_get(v_e_1532_, 0);
v___x_1534_ = l_Lean_Name_hasMacroScopes(v_declName_1533_);
return v___x_1534_;
}
else
{
uint8_t v___x_1535_; 
v___x_1535_ = 0;
return v___x_1535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0___boxed(lean_object* v_e_1536_){
_start:
{
uint8_t v_res_1537_; lean_object* v_r_1538_; 
v_res_1537_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0(v_e_1536_);
lean_dec_ref(v_e_1536_);
v_r_1538_ = lean_box(v_res_1537_);
return v_r_1538_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(lean_object* v_as_1539_, size_t v_i_1540_, size_t v_stop_1541_){
_start:
{
uint8_t v___x_1542_; 
v___x_1542_ = lean_usize_dec_eq(v_i_1540_, v_stop_1541_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_array_uget_borrowed(v_as_1539_, v_i_1540_);
if (lean_obj_tag(v___x_1543_) == 0)
{
uint8_t v___x_1544_; 
v___x_1544_ = 1;
return v___x_1544_;
}
else
{
size_t v___x_1545_; size_t v___x_1546_; 
v___x_1545_ = ((size_t)1ULL);
v___x_1546_ = lean_usize_add(v_i_1540_, v___x_1545_);
v_i_1540_ = v___x_1546_;
goto _start;
}
}
else
{
uint8_t v___x_1548_; 
v___x_1548_ = 0;
return v___x_1548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5___boxed(lean_object* v_as_1549_, lean_object* v_i_1550_, lean_object* v_stop_1551_){
_start:
{
size_t v_i_boxed_1552_; size_t v_stop_boxed_1553_; uint8_t v_res_1554_; lean_object* v_r_1555_; 
v_i_boxed_1552_ = lean_unbox_usize(v_i_1550_);
lean_dec(v_i_1550_);
v_stop_boxed_1553_ = lean_unbox_usize(v_stop_1551_);
lean_dec(v_stop_1551_);
v_res_1554_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(v_as_1549_, v_i_boxed_1552_, v_stop_boxed_1553_);
lean_dec_ref(v_as_1549_);
v_r_1555_ = lean_box(v_res_1554_);
return v_r_1555_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(lean_object* v___x_1556_, lean_object* v_as_1557_, size_t v_i_1558_, size_t v_stop_1559_){
_start:
{
uint8_t v___x_1560_; 
v___x_1560_ = lean_usize_dec_eq(v_i_1558_, v_stop_1559_);
if (v___x_1560_ == 0)
{
uint8_t v___x_1561_; lean_object* v___y_1563_; lean_object* v___x_1569_; 
v___x_1561_ = 1;
v___x_1569_ = lean_array_uget(v_as_1557_, v_i_1558_);
if (lean_obj_tag(v___x_1569_) == 0)
{
v___y_1563_ = v___x_1569_;
goto v___jp_1562_;
}
else
{
lean_object* v_val_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1578_; 
v_val_1570_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1572_ = v___x_1569_;
v_isShared_1573_ = v_isSharedCheck_1578_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_val_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1578_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1574_ = l_Lean_Name_getRoot(v_val_1570_);
lean_dec(v_val_1570_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v___x_1574_);
v___x_1576_ = v___x_1572_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
v___y_1563_ = v___x_1576_;
goto v___jp_1562_;
}
}
}
v___jp_1562_:
{
lean_object* v___x_1564_; uint8_t v___x_1565_; 
lean_inc(v___x_1556_);
v___x_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1556_);
v___x_1565_ = l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(v___y_1563_, v___x_1564_);
lean_dec_ref_known(v___x_1564_, 1);
lean_dec(v___y_1563_);
if (v___x_1565_ == 0)
{
size_t v___x_1566_; size_t v___x_1567_; 
v___x_1566_ = ((size_t)1ULL);
v___x_1567_ = lean_usize_add(v_i_1558_, v___x_1566_);
v_i_1558_ = v___x_1567_;
goto _start;
}
else
{
lean_dec(v___x_1556_);
return v___x_1561_;
}
}
}
else
{
uint8_t v___x_1579_; 
lean_dec(v___x_1556_);
v___x_1579_ = 0;
return v___x_1579_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4___boxed(lean_object* v___x_1580_, lean_object* v_as_1581_, lean_object* v_i_1582_, lean_object* v_stop_1583_){
_start:
{
size_t v_i_boxed_1584_; size_t v_stop_boxed_1585_; uint8_t v_res_1586_; lean_object* v_r_1587_; 
v_i_boxed_1584_ = lean_unbox_usize(v_i_1582_);
lean_dec(v_i_1582_);
v_stop_boxed_1585_ = lean_unbox_usize(v_stop_1583_);
lean_dec(v_stop_1583_);
v_res_1586_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(v___x_1580_, v_as_1581_, v_i_boxed_1584_, v_stop_boxed_1585_);
lean_dec_ref(v_as_1581_);
v_r_1587_ = lean_box(v_res_1586_);
return v_r_1587_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1588_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
return v___x_1590_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1591_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_1592_ = lean_unsigned_to_nat(0u);
v___x_1593_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
lean_ctor_set(v___x_1593_, 2, v___x_1592_);
lean_ctor_set(v___x_1593_, 3, v___x_1592_);
lean_ctor_set(v___x_1593_, 4, v___x_1591_);
lean_ctor_set(v___x_1593_, 5, v___x_1591_);
lean_ctor_set(v___x_1593_, 6, v___x_1591_);
lean_ctor_set(v___x_1593_, 7, v___x_1591_);
lean_ctor_set(v___x_1593_, 8, v___x_1591_);
lean_ctor_set(v___x_1593_, 9, v___x_1591_);
lean_ctor_set(v___x_1593_, 10, v___x_1591_);
return v___x_1593_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1594_ = lean_unsigned_to_nat(32u);
v___x_1595_ = lean_mk_empty_array_with_capacity(v___x_1594_);
v___x_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
return v___x_1596_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1597_ = ((size_t)5ULL);
v___x_1598_ = lean_unsigned_to_nat(0u);
v___x_1599_ = lean_unsigned_to_nat(32u);
v___x_1600_ = lean_mk_empty_array_with_capacity(v___x_1599_);
v___x_1601_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_1602_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
lean_ctor_set(v___x_1602_, 1, v___x_1600_);
lean_ctor_set(v___x_1602_, 2, v___x_1598_);
lean_ctor_set(v___x_1602_, 3, v___x_1598_);
lean_ctor_set_usize(v___x_1602_, 4, v___x_1597_);
return v___x_1602_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1603_ = lean_box(1);
v___x_1604_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_1605_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_1606_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
lean_ctor_set(v___x_1606_, 1, v___x_1604_);
lean_ctor_set(v___x_1606_, 2, v___x_1603_);
return v___x_1606_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_1609_ = l_Lean_stringToMessageData(v___x_1608_);
return v___x_1609_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_1612_ = l_Lean_stringToMessageData(v___x_1611_);
return v___x_1612_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_1615_ = l_Lean_stringToMessageData(v___x_1614_);
return v___x_1615_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_1618_ = l_Lean_stringToMessageData(v___x_1617_);
return v___x_1618_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__14));
v___x_1621_ = l_Lean_stringToMessageData(v___x_1620_);
return v___x_1621_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__16));
v___x_1624_ = l_Lean_stringToMessageData(v___x_1623_);
return v___x_1624_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__18));
v___x_1627_ = l_Lean_stringToMessageData(v___x_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_1628_, lean_object* v_declHint_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v___x_1632_; lean_object* v_env_1633_; uint8_t v___x_1634_; 
v___x_1632_ = lean_st_ref_get(v___y_1630_);
v_env_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc_ref(v_env_1633_);
lean_dec(v___x_1632_);
v___x_1634_ = l_Lean_Name_isAnonymous(v_declHint_1629_);
if (v___x_1634_ == 0)
{
uint8_t v_isExporting_1635_; 
v_isExporting_1635_ = lean_ctor_get_uint8(v_env_1633_, sizeof(void*)*8);
if (v_isExporting_1635_ == 0)
{
lean_object* v___x_1636_; 
lean_dec_ref(v_env_1633_);
lean_dec(v_declHint_1629_);
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v_msg_1628_);
return v___x_1636_;
}
else
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
lean_inc_ref(v_env_1633_);
v___x_1637_ = l_Lean_Environment_setExporting(v_env_1633_, v___x_1634_);
lean_inc(v_declHint_1629_);
lean_inc_ref(v___x_1637_);
v___x_1638_ = l_Lean_Environment_contains(v___x_1637_, v_declHint_1629_, v_isExporting_1635_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; 
lean_dec_ref(v___x_1637_);
lean_dec_ref(v_env_1633_);
lean_dec(v_declHint_1629_);
v___x_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1639_, 0, v_msg_1628_);
return v___x_1639_;
}
else
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v_c_1645_; lean_object* v___x_1646_; 
v___x_1640_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_1641_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5);
v___x_1642_ = l_Lean_Options_empty;
v___x_1643_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1637_);
lean_ctor_set(v___x_1643_, 1, v___x_1640_);
lean_ctor_set(v___x_1643_, 2, v___x_1641_);
lean_ctor_set(v___x_1643_, 3, v___x_1642_);
lean_inc(v_declHint_1629_);
v___x_1644_ = l_Lean_MessageData_ofConstName(v_declHint_1629_, v___x_1634_);
v_c_1645_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1645_, 0, v___x_1643_);
lean_ctor_set(v_c_1645_, 1, v___x_1644_);
v___x_1646_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1633_, v_declHint_1629_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_dec_ref(v_env_1633_);
lean_dec(v_declHint_1629_);
v___x_1647_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_1648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
lean_ctor_set(v___x_1648_, 1, v_c_1645_);
v___x_1649_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = l_Lean_MessageData_note(v___x_1650_);
v___x_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1652_, 0, v_msg_1628_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
return v___x_1653_;
}
else
{
lean_object* v_val_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1689_; 
v_val_1654_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1656_ = v___x_1646_;
v_isShared_1657_ = v_isSharedCheck_1689_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_val_1654_);
lean_dec(v___x_1646_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1689_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v_mod_1661_; uint8_t v___x_1662_; 
v___x_1658_ = lean_box(0);
v___x_1659_ = l_Lean_Environment_header(v_env_1633_);
lean_dec_ref(v_env_1633_);
v___x_1660_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1659_);
v_mod_1661_ = lean_array_get(v___x_1658_, v___x_1660_, v_val_1654_);
lean_dec(v_val_1654_);
lean_dec_ref(v___x_1660_);
v___x_1662_ = l_Lean_isPrivateName(v_declHint_1629_);
lean_dec(v_declHint_1629_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1663_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_1664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
lean_ctor_set(v___x_1664_, 1, v_c_1645_);
v___x_1665_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_1666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1664_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = l_Lean_MessageData_ofName(v_mod_1661_);
v___x_1668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1666_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
v___x_1669_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_1670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1668_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = l_Lean_MessageData_note(v___x_1670_);
v___x_1672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1672_, 0, v_msg_1628_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set_tag(v___x_1656_, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1672_);
v___x_1674_ = v___x_1656_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1676_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_1677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set(v___x_1677_, 1, v_c_1645_);
v___x_1678_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17);
v___x_1679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = l_Lean_MessageData_ofName(v_mod_1661_);
v___x_1681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19);
v___x_1683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1681_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
v___x_1684_ = l_Lean_MessageData_note(v___x_1683_);
v___x_1685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1685_, 0, v_msg_1628_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set_tag(v___x_1656_, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1685_);
v___x_1687_ = v___x_1656_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1690_; 
lean_dec_ref(v_env_1633_);
lean_dec(v_declHint_1629_);
v___x_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1690_, 0, v_msg_1628_);
return v___x_1690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_1691_, lean_object* v_declHint_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_1691_, v_declHint_1692_, v___y_1693_);
lean_dec(v___y_1693_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(lean_object* v_msg_1696_, lean_object* v_declHint_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v___x_1703_; lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1713_; 
v___x_1703_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_1696_, v_declHint_1697_, v___y_1701_);
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1706_ = v___x_1703_;
v_isShared_1707_ = v_isSharedCheck_1713_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1703_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1713_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1708_ = l_Lean_unknownIdentifierMessageTag;
v___x_1709_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1708_);
lean_ctor_set(v___x_1709_, 1, v_a_1704_);
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 0, v___x_1709_);
v___x_1711_ = v___x_1706_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1714_, lean_object* v_declHint_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(v_msg_1714_, v_declHint_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(lean_object* v_ref_1722_, lean_object* v_msg_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v_toCold_1729_; lean_object* v_currRecDepth_1730_; lean_object* v_ref_1731_; uint8_t v_diag_1732_; uint8_t v_suppressElabErrors_1733_; lean_object* v_ref_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v_toCold_1729_ = lean_ctor_get(v___y_1726_, 0);
v_currRecDepth_1730_ = lean_ctor_get(v___y_1726_, 1);
v_ref_1731_ = lean_ctor_get(v___y_1726_, 2);
v_diag_1732_ = lean_ctor_get_uint8(v___y_1726_, sizeof(void*)*3);
v_suppressElabErrors_1733_ = lean_ctor_get_uint8(v___y_1726_, sizeof(void*)*3 + 1);
v_ref_1734_ = l_Lean_replaceRef(v_ref_1722_, v_ref_1731_);
lean_inc(v_currRecDepth_1730_);
lean_inc_ref(v_toCold_1729_);
v___x_1735_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1735_, 0, v_toCold_1729_);
lean_ctor_set(v___x_1735_, 1, v_currRecDepth_1730_);
lean_ctor_set(v___x_1735_, 2, v_ref_1734_);
lean_ctor_set_uint8(v___x_1735_, sizeof(void*)*3, v_diag_1732_);
lean_ctor_set_uint8(v___x_1735_, sizeof(void*)*3 + 1, v_suppressElabErrors_1733_);
v___x_1736_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v_msg_1723_, v___y_1724_, v___y_1725_, v___x_1735_, v___y_1727_);
lean_dec_ref_known(v___x_1735_, 3);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_ref_1737_, lean_object* v_msg_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_1737_, v_msg_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v_ref_1737_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(lean_object* v_ref_1745_, lean_object* v_msg_1746_, lean_object* v_declHint_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v___x_1753_; lean_object* v_a_1754_; lean_object* v___x_1755_; 
v___x_1753_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(v_msg_1746_, v_declHint_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref(v___x_1753_);
v___x_1755_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_1745_, v_a_1754_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg___boxed(lean_object* v_ref_1756_, lean_object* v_msg_1757_, lean_object* v_declHint_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_1756_, v_msg_1757_, v_declHint_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v_ref_1756_);
return v_res_1764_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__0));
v___x_1767_ = l_Lean_stringToMessageData(v___x_1766_);
return v___x_1767_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__2));
v___x_1770_ = l_Lean_stringToMessageData(v___x_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_ref_1771_, lean_object* v_constName_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v___x_1778_; uint8_t v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1778_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1);
v___x_1779_ = 0;
lean_inc(v_constName_1772_);
v___x_1780_ = l_Lean_MessageData_ofConstName(v_constName_1772_, v___x_1779_);
v___x_1781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1778_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3);
v___x_1783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1781_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_1771_, v___x_1783_, v_constName_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v_ref_1785_, lean_object* v_constName_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1785_, v_constName_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v_ref_1785_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(lean_object* v_constName_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_ref_1799_; lean_object* v___x_1800_; 
v_ref_1799_ = lean_ctor_get(v___y_1796_, 2);
v___x_1800_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1799_, v_constName_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_constName_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(lean_object* v_constName_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v___x_1814_; lean_object* v_env_1815_; uint8_t v___x_1816_; lean_object* v___x_1817_; 
v___x_1814_ = lean_st_ref_get(v___y_1812_);
v_env_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc_ref(v_env_1815_);
lean_dec(v___x_1814_);
v___x_1816_ = 0;
lean_inc(v_constName_1808_);
v___x_1817_ = l_Lean_Environment_find_x3f(v_env_1815_, v_constName_1808_, v___x_1816_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
return v___x_1818_;
}
else
{
lean_object* v_val_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec(v_constName_1808_);
v_val_1819_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1817_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_val_1819_);
lean_dec(v___x_1817_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
lean_ctor_set_tag(v___x_1821_, 0);
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_val_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0___boxed(lean_object* v_constName_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(v_constName_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(lean_object* v_declName_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v___x_1840_; 
lean_inc(v_declName_1834_);
v___x_1840_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(v_declName_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1867_; 
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1867_ == 0)
{
lean_object* v_unused_1868_; 
v_unused_1868_ = lean_ctor_get(v___x_1840_, 0);
lean_dec(v_unused_1868_);
v___x_1842_ = v___x_1840_;
v_isShared_1843_ = v_isSharedCheck_1867_;
goto v_resetjp_1841_;
}
else
{
lean_dec(v___x_1840_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1867_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; lean_object* v_env_1845_; lean_object* v___x_1846_; 
v___x_1844_ = lean_st_ref_get(v___y_1838_);
v_env_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc_ref(v_env_1845_);
lean_dec(v___x_1844_);
v___x_1846_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1845_, v_declName_1834_);
lean_dec(v_declName_1834_);
lean_dec_ref(v_env_1845_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1847_ = lean_box(0);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1847_);
v___x_1849_ = v___x_1842_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
else
{
lean_object* v_val_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1866_; 
v_val_1851_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1853_ = v___x_1846_;
v_isShared_1854_ = v_isSharedCheck_1866_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_val_1851_);
lean_dec(v___x_1846_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1866_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1855_; lean_object* v_env_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1855_ = lean_st_ref_get(v___y_1838_);
v_env_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc_ref(v_env_1856_);
lean_dec(v___x_1855_);
v___x_1857_ = lean_box(0);
v___x_1858_ = l_Lean_Environment_allImportedModuleNames(v_env_1856_);
lean_dec_ref(v_env_1856_);
v___x_1859_ = lean_array_get(v___x_1857_, v___x_1858_, v_val_1851_);
lean_dec(v_val_1851_);
lean_dec_ref(v___x_1858_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v___x_1859_);
v___x_1861_ = v___x_1853_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1863_; 
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1861_);
v___x_1863_ = v___x_1842_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_declName_1834_);
v_a_1869_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1840_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1840_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0___boxed(lean_object* v_declName_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(v_declName_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(lean_object* v_init_1884_, lean_object* v_x_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
if (lean_obj_tag(v_x_1885_) == 0)
{
lean_object* v_k_1891_; lean_object* v_l_1892_; lean_object* v_r_1893_; lean_object* v___x_1894_; 
v_k_1891_ = lean_ctor_get(v_x_1885_, 1);
lean_inc(v_k_1891_);
v_l_1892_ = lean_ctor_get(v_x_1885_, 3);
lean_inc(v_l_1892_);
v_r_1893_ = lean_ctor_get(v_x_1885_, 4);
lean_inc(v_r_1893_);
lean_dec_ref_known(v_x_1885_, 5);
v___x_1894_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v_init_1884_, v_l_1892_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1896_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_a_1895_);
lean_dec_ref_known(v___x_1894_, 1);
v___x_1896_ = l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(v_k_1891_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1898_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref_known(v___x_1896_, 1);
v___x_1898_ = lean_array_push(v_a_1895_, v_a_1897_);
v_init_1884_ = v___x_1898_;
v_x_1885_ = v_r_1893_;
goto _start;
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
lean_dec(v_a_1895_);
lean_dec(v_r_1893_);
v_a_1900_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1896_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1896_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
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
else
{
lean_dec(v_r_1893_);
lean_dec(v_k_1891_);
return v___x_1894_;
}
}
else
{
lean_object* v___x_1908_; 
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v_init_1884_);
return v___x_1908_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3___boxed(lean_object* v_init_1909_, lean_object* v_x_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v_init_1909_, v_x_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
return v_res_1916_;
}
}
static lean_object* _init_l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0(void){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = l_Lean_NameSet_empty;
v___x_1918_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1);
v___x_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v___x_1917_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(lean_object* v_pre_1921_, lean_object* v_type_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1928_ = lean_unsigned_to_nat(0u);
v___x_1929_ = lean_obj_once(&l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0, &l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0_once, _init_l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0);
v___x_1930_ = lean_st_mk_ref(v___x_1929_);
lean_inc_ref(v_type_1922_);
v___x_1931_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(v_type_1922_, v___x_1930_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1981_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1931_, 1);
v___x_1933_ = lean_st_ref_get(v___x_1930_);
lean_dec(v___x_1930_);
v___x_1934_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v_a_1926_);
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1937_ = v___x_1934_;
v_isShared_1938_ = v_isSharedCheck_1981_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1981_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v_consts_1939_; lean_object* v___f_1940_; lean_object* v___y_1942_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1963_; 
v_consts_1939_ = lean_ctor_get(v___x_1933_, 1);
lean_inc(v_consts_1939_);
lean_dec(v___x_1933_);
v___f_1940_ = ((lean_object*)(l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1));
v___x_1950_ = lean_string_append(v_pre_1921_, v_a_1932_);
lean_dec(v_a_1932_);
v___x_1951_ = l_Lean_Name_getRoot(v_a_1935_);
lean_dec(v_a_1935_);
if (lean_obj_tag(v_consts_1939_) == 0)
{
lean_object* v_size_1980_; 
v_size_1980_ = lean_ctor_get(v_consts_1939_, 0);
lean_inc(v_size_1980_);
v___y_1963_ = v_size_1980_;
goto v___jp_1962_;
}
else
{
v___y_1963_ = v___x_1928_;
goto v___jp_1962_;
}
v___jp_1941_:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1943_ = lean_box(0);
v___x_1944_ = l_Lean_Name_str___override(v___x_1943_, v___y_1942_);
v___x_1945_ = lean_find_expr(v___f_1940_, v_type_1922_);
lean_dec_ref(v_type_1922_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v___x_1947_; 
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 0, v___x_1944_);
v___x_1947_ = v___x_1937_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1944_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
else
{
lean_object* v___x_1949_; 
lean_dec_ref_known(v___x_1945_, 1);
lean_del_object(v___x_1937_);
v___x_1949_ = l_Lean_Core_mkFreshUserName(v___x_1944_, v_a_1925_, v_a_1926_);
return v___x_1949_;
}
}
v___jp_1952_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(v___x_1951_);
v___x_1954_ = lean_string_append(v___x_1950_, v___x_1953_);
lean_dec_ref(v___x_1953_);
v___y_1942_ = v___x_1954_;
goto v___jp_1941_;
}
v___jp_1955_:
{
uint8_t v___x_1958_; 
v___x_1958_ = lean_nat_dec_lt(v___x_1928_, v___y_1956_);
if (v___x_1958_ == 0)
{
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
goto v___jp_1952_;
}
else
{
if (v___x_1958_ == 0)
{
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
goto v___jp_1952_;
}
else
{
size_t v___x_1959_; size_t v___x_1960_; uint8_t v___x_1961_; 
v___x_1959_ = ((size_t)0ULL);
v___x_1960_ = lean_usize_of_nat(v___y_1956_);
lean_dec(v___y_1956_);
lean_inc(v___x_1951_);
v___x_1961_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(v___x_1951_, v___y_1957_, v___x_1959_, v___x_1960_);
lean_dec_ref(v___y_1957_);
if (v___x_1961_ == 0)
{
goto v___jp_1952_;
}
else
{
lean_dec(v___x_1951_);
v___y_1942_ = v___x_1950_;
goto v___jp_1941_;
}
}
}
}
v___jp_1962_:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = lean_mk_empty_array_with_capacity(v___y_1963_);
lean_dec(v___y_1963_);
v___x_1965_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v___x_1964_, v_consts_1939_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref_known(v___x_1965_, 1);
v___x_1967_ = lean_array_get_size(v_a_1966_);
v___x_1968_ = lean_nat_dec_lt(v___x_1928_, v___x_1967_);
if (v___x_1968_ == 0)
{
v___y_1956_ = v___x_1967_;
v___y_1957_ = v_a_1966_;
goto v___jp_1955_;
}
else
{
if (v___x_1968_ == 0)
{
v___y_1956_ = v___x_1967_;
v___y_1957_ = v_a_1966_;
goto v___jp_1955_;
}
else
{
size_t v___x_1969_; size_t v___x_1970_; uint8_t v___x_1971_; 
v___x_1969_ = ((size_t)0ULL);
v___x_1970_ = lean_usize_of_nat(v___x_1967_);
v___x_1971_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(v_a_1966_, v___x_1969_, v___x_1970_);
if (v___x_1971_ == 0)
{
v___y_1956_ = v___x_1967_;
v___y_1957_ = v_a_1966_;
goto v___jp_1955_;
}
else
{
lean_dec(v_a_1966_);
lean_dec(v___x_1951_);
v___y_1942_ = v___x_1950_;
goto v___jp_1941_;
}
}
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec(v___x_1951_);
lean_dec_ref(v___x_1950_);
lean_del_object(v___x_1937_);
lean_dec_ref(v_type_1922_);
v_a_1972_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1965_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1965_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
lean_dec(v___x_1930_);
lean_dec_ref(v_type_1922_);
lean_dec_ref(v_pre_1921_);
v_a_1982_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1931_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1931_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___boxed(lean_object* v_pre_1990_, lean_object* v_type_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(v_pre_1990_, v_type_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_);
lean_dec(v_a_1995_);
lean_dec_ref(v_a_1994_);
lean_dec(v_a_1993_);
lean_dec_ref(v_a_1992_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1998_, lean_object* v_constName_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_2006_, lean_object* v_constName_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3(v_00_u03b1_2006_, v_constName_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b1_2014_, lean_object* v_ref_2015_, lean_object* v_constName_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_2015_, v_constName_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_00_u03b1_2023_, lean_object* v_ref_2024_, lean_object* v_constName_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7(v_00_u03b1_2023_, v_ref_2024_, v_constName_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v_ref_2024_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8(lean_object* v_00_u03b1_2032_, lean_object* v_ref_2033_, lean_object* v_msg_2034_, lean_object* v_declHint_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v___x_2041_; 
v___x_2041_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_2033_, v_msg_2034_, v_declHint_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___boxed(lean_object* v_00_u03b1_2042_, lean_object* v_ref_2043_, lean_object* v_msg_2044_, lean_object* v_declHint_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8(v_00_u03b1_2042_, v_ref_2043_, v_msg_2044_, v_declHint_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v_ref_2043_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10(lean_object* v_msg_2052_, lean_object* v_declHint_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_2052_, v_declHint_2053_, v___y_2057_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_2060_, lean_object* v_declHint_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10(v_msg_2060_, v_declHint_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_2068_, lean_object* v_ref_2069_, lean_object* v_msg_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_2069_, v_msg_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_2077_, lean_object* v_ref_2078_, lean_object* v_msg_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10(v_00_u03b1_2077_, v_ref_2078_, v_msg_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v_ref_2078_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg(lean_object* v_a_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg___boxed(lean_object* v_a_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg(v_a_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0(lean_object* v_00_u03b1_2104_, lean_object* v_a_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___boxed(lean_object* v_00_u03b1_2114_, lean_object* v_a_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0(v_00_u03b1_2114_, v_a_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0(lean_object* v_type_2124_, lean_object* v_binds_2125_, lean_object* v_pre_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Lean_Elab_Term_elabType(v_type_2124_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; uint8_t v___x_2136_; uint8_t v___x_2137_; uint8_t v___x_2138_; lean_object* v___x_2139_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v___x_2136_ = 0;
v___x_2137_ = 1;
v___x_2138_ = 1;
v___x_2139_ = l_Lean_Meta_mkForallFVars(v_binds_2125_, v_a_2135_, v___x_2136_, v___x_2137_, v___x_2137_, v___x_2138_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
v___x_2141_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(v_pre_2126_, v_a_2140_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
return v___x_2141_;
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec_ref(v_pre_2126_);
v_a_2142_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2139_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2139_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_dec_ref(v_pre_2126_);
v_a_2150_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2134_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2134_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0___boxed(lean_object* v_type_2158_, lean_object* v_binds_2159_, lean_object* v_pre_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0(v_type_2158_, v_binds_2159_, v_pre_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec_ref(v_binds_2159_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1(lean_object* v_type_2169_, lean_object* v_pre_2170_, lean_object* v_binds_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v___f_2179_; lean_object* v___x_2180_; 
v___f_2179_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2179_, 0, v_type_2169_);
lean_closure_set(v___f_2179_, 1, v_binds_2171_);
lean_closure_set(v___f_2179_, 2, v_pre_2170_);
v___x_2180_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_2179_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1___boxed(lean_object* v_type_2181_, lean_object* v_pre_2182_, lean_object* v_binds_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1(v_type_2181_, v_pre_2182_, v_binds_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3(lean_object* v_currNamespace_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2195_, 0, v_currNamespace_2192_);
lean_ctor_set(v___x_2195_, 1, v___y_2194_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3___boxed(lean_object* v_currNamespace_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3(v_currNamespace_2196_, v___y_2197_, v___y_2198_);
lean_dec_ref(v___y_2197_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1(lean_object* v_env_2200_, lean_object* v_declName_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
uint8_t v___x_2204_; lean_object* v_env_2205_; lean_object* v___x_2206_; uint8_t v___x_2207_; uint8_t v___x_2208_; 
v___x_2204_ = 0;
v_env_2205_ = l_Lean_Environment_setExporting(v_env_2200_, v___x_2204_);
lean_inc(v_declName_2201_);
v___x_2206_ = l_Lean_mkPrivateName(v_env_2205_, v_declName_2201_);
v___x_2207_ = 1;
lean_inc_ref(v_env_2205_);
v___x_2208_ = l_Lean_Environment_contains(v_env_2205_, v___x_2206_, v___x_2207_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; uint8_t v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2209_ = l_Lean_privateToUserName(v_declName_2201_);
v___x_2210_ = l_Lean_Environment_contains(v_env_2205_, v___x_2209_, v___x_2207_);
v___x_2211_ = lean_box(v___x_2210_);
v___x_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
lean_ctor_set(v___x_2212_, 1, v___y_2203_);
return v___x_2212_;
}
else
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
lean_dec_ref(v_env_2205_);
lean_dec(v_declName_2201_);
v___x_2213_ = lean_box(v___x_2208_);
v___x_2214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
lean_ctor_set(v___x_2214_, 1, v___y_2203_);
return v___x_2214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1___boxed(lean_object* v_env_2215_, lean_object* v_declName_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1(v_env_2215_, v_declName_2216_, v___y_2217_, v___y_2218_);
lean_dec_ref(v___y_2217_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(lean_object* v_x_2220_, lean_object* v___y_2221_){
_start:
{
if (lean_obj_tag(v_x_2220_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2223_; 
v_a_2222_ = lean_ctor_get(v_x_2220_, 0);
lean_inc(v_a_2222_);
v___x_2223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2223_, 0, v_a_2222_);
lean_ctor_set(v___x_2223_, 1, v___y_2221_);
return v___x_2223_;
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2225_; 
v_a_2224_ = lean_ctor_get(v_x_2220_, 0);
lean_inc(v_a_2224_);
v___x_2225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2225_, 0, v_a_2224_);
lean_ctor_set(v___x_2225_, 1, v___y_2221_);
return v___x_2225_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg___boxed(lean_object* v_x_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v_x_2226_, v___y_2227_);
lean_dec_ref(v_x_2226_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0(lean_object* v_env_2229_, lean_object* v_stx_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2229_, v_stx_2230_, v___y_2231_, v___y_2232_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2234_);
if (lean_obj_tag(v_a_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2243_; 
v_a_2235_ = lean_ctor_get(v___x_2233_, 1);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2243_ == 0)
{
lean_object* v_unused_2244_; 
v_unused_2244_ = lean_ctor_get(v___x_2233_, 0);
lean_dec(v_unused_2244_);
v___x_2237_ = v___x_2233_;
v_isShared_2238_ = v_isSharedCheck_2243_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2233_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2243_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2239_; lean_object* v___x_2241_; 
v___x_2239_ = lean_box(0);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 0, v___x_2239_);
v___x_2241_ = v___x_2237_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2239_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v_a_2235_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
else
{
lean_object* v_val_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2273_; 
v_val_2245_ = lean_ctor_get(v_a_2234_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v_a_2234_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2247_ = v_a_2234_;
v_isShared_2248_ = v_isSharedCheck_2273_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_val_2245_);
lean_dec(v_a_2234_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2273_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v_snd_2249_; 
v_snd_2249_ = lean_ctor_get(v_val_2245_, 1);
lean_inc(v_snd_2249_);
lean_dec(v_val_2245_);
if (lean_obj_tag(v_snd_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2259_; 
lean_del_object(v___x_2247_);
v_a_2250_ = lean_ctor_get(v___x_2233_, 1);
lean_inc(v_a_2250_);
lean_dec_ref_known(v___x_2233_, 2);
v_a_2251_ = lean_ctor_get(v_snd_2249_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_snd_2249_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2253_ = v_snd_2249_;
v_isShared_2254_ = v_isSharedCheck_2259_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v_snd_2249_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2259_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
lean_object* v___x_2257_; 
v___x_2257_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v___x_2256_, v_a_2250_);
lean_dec_ref(v___x_2256_);
return v___x_2257_;
}
}
}
else
{
lean_object* v_a_2260_; lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2272_; 
v_a_2260_ = lean_ctor_get(v___x_2233_, 1);
lean_inc(v_a_2260_);
lean_dec_ref_known(v___x_2233_, 2);
v_a_2261_ = lean_ctor_get(v_snd_2249_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v_snd_2249_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2263_ = v_snd_2249_;
v_isShared_2264_ = v_isSharedCheck_2272_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v_snd_2249_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2272_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v_a_2261_);
v___x_2266_ = v___x_2247_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v___x_2268_; 
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 0, v___x_2266_);
v___x_2268_ = v___x_2263_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2266_);
v___x_2268_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v___x_2268_, v_a_2260_);
lean_dec_ref(v___x_2268_);
return v___x_2269_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2274_; lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
v_a_2274_ = lean_ctor_get(v___x_2233_, 0);
v_a_2275_ = lean_ctor_get(v___x_2233_, 1);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2233_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_inc(v_a_2274_);
lean_dec(v___x_2233_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2274_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_a_2275_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0___boxed(lean_object* v_env_2283_, lean_object* v_stx_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0(v_env_2283_, v_stx_2284_, v___y_2285_, v___y_2286_);
lean_dec_ref(v___y_2285_);
return v_res_2287_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17(lean_object* v_opts_2288_, lean_object* v_opt_2289_){
_start:
{
lean_object* v_name_2290_; lean_object* v_defValue_2291_; lean_object* v_map_2292_; lean_object* v___x_2293_; 
v_name_2290_ = lean_ctor_get(v_opt_2289_, 0);
v_defValue_2291_ = lean_ctor_get(v_opt_2289_, 1);
v_map_2292_ = lean_ctor_get(v_opts_2288_, 0);
v___x_2293_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2292_, v_name_2290_);
if (lean_obj_tag(v___x_2293_) == 0)
{
uint8_t v___x_2294_; 
v___x_2294_ = lean_unbox(v_defValue_2291_);
return v___x_2294_;
}
else
{
lean_object* v_val_2295_; 
v_val_2295_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_val_2295_);
lean_dec_ref_known(v___x_2293_, 1);
if (lean_obj_tag(v_val_2295_) == 1)
{
uint8_t v_v_2296_; 
v_v_2296_ = lean_ctor_get_uint8(v_val_2295_, 0);
lean_dec_ref_known(v_val_2295_, 0);
return v_v_2296_;
}
else
{
uint8_t v___x_2297_; 
lean_dec(v_val_2295_);
v___x_2297_ = lean_unbox(v_defValue_2291_);
return v___x_2297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17___boxed(lean_object* v_opts_2298_, lean_object* v_opt_2299_){
_start:
{
uint8_t v_res_2300_; lean_object* v_r_2301_; 
v_res_2300_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17(v_opts_2298_, v_opt_2299_);
lean_dec_ref(v_opt_2299_);
lean_dec_ref(v_opts_2298_);
v_r_2301_ = lean_box(v_res_2300_);
return v_r_2301_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = lean_box(1);
v___x_2303_ = l_Lean_MessageData_ofFormat(v___x_2302_);
return v___x_2303_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3(void){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__2));
v___x_2308_ = l_Lean_MessageData_ofFormat(v___x_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18(lean_object* v_x_2309_, lean_object* v_x_2310_){
_start:
{
if (lean_obj_tag(v_x_2310_) == 0)
{
return v_x_2309_;
}
else
{
lean_object* v_head_2311_; lean_object* v_tail_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2334_; 
v_head_2311_ = lean_ctor_get(v_x_2310_, 0);
v_tail_2312_ = lean_ctor_get(v_x_2310_, 1);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_x_2310_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2314_ = v_x_2310_;
v_isShared_2315_ = v_isSharedCheck_2334_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_tail_2312_);
lean_inc(v_head_2311_);
lean_dec(v_x_2310_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2334_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v_before_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2332_; 
v_before_2316_ = lean_ctor_get(v_head_2311_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v_head_2311_);
if (v_isSharedCheck_2332_ == 0)
{
lean_object* v_unused_2333_; 
v_unused_2333_ = lean_ctor_get(v_head_2311_, 1);
lean_dec(v_unused_2333_);
v___x_2318_ = v_head_2311_;
v_isShared_2319_ = v_isSharedCheck_2332_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_before_2316_);
lean_dec(v_head_2311_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2332_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2320_; lean_object* v___x_2322_; 
v___x_2320_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0);
if (v_isShared_2319_ == 0)
{
lean_ctor_set_tag(v___x_2318_, 7);
lean_ctor_set(v___x_2318_, 1, v___x_2320_);
lean_ctor_set(v___x_2318_, 0, v_x_2309_);
v___x_2322_ = v___x_2318_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_x_2309_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v___x_2320_);
v___x_2322_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
lean_object* v___x_2323_; lean_object* v___x_2325_; 
v___x_2323_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3);
if (v_isShared_2315_ == 0)
{
lean_ctor_set_tag(v___x_2314_, 7);
lean_ctor_set(v___x_2314_, 1, v___x_2323_);
lean_ctor_set(v___x_2314_, 0, v___x_2322_);
v___x_2325_ = v___x_2314_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2322_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2326_ = l_Lean_MessageData_ofSyntax(v_before_2316_);
v___x_2327_ = l_Lean_indentD(v___x_2326_);
v___x_2328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2325_);
lean_ctor_set(v___x_2328_, 1, v___x_2327_);
v_x_2309_ = v___x_2328_;
v_x_2310_ = v_tail_2312_;
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
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__1));
v___x_2339_ = l_Lean_MessageData_ofFormat(v___x_2338_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(lean_object* v_msgData_2340_, lean_object* v_macroStack_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v_toCold_2344_; lean_object* v_options_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; 
v_toCold_2344_ = lean_ctor_get(v___y_2342_, 0);
v_options_2345_ = lean_ctor_get(v_toCold_2344_, 2);
v___x_2346_ = l_Lean_Elab_pp_macroStack;
v___x_2347_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17(v_options_2345_, v___x_2346_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; 
lean_dec(v_macroStack_2341_);
v___x_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2348_, 0, v_msgData_2340_);
return v___x_2348_;
}
else
{
if (lean_obj_tag(v_macroStack_2341_) == 0)
{
lean_object* v___x_2349_; 
v___x_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2349_, 0, v_msgData_2340_);
return v___x_2349_;
}
else
{
lean_object* v_head_2350_; lean_object* v_after_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2366_; 
v_head_2350_ = lean_ctor_get(v_macroStack_2341_, 0);
lean_inc(v_head_2350_);
v_after_2351_ = lean_ctor_get(v_head_2350_, 1);
v_isSharedCheck_2366_ = !lean_is_exclusive(v_head_2350_);
if (v_isSharedCheck_2366_ == 0)
{
lean_object* v_unused_2367_; 
v_unused_2367_ = lean_ctor_get(v_head_2350_, 0);
lean_dec(v_unused_2367_);
v___x_2353_ = v_head_2350_;
v_isShared_2354_ = v_isSharedCheck_2366_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_after_2351_);
lean_dec(v_head_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2366_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2355_; lean_object* v___x_2357_; 
v___x_2355_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0);
if (v_isShared_2354_ == 0)
{
lean_ctor_set_tag(v___x_2353_, 7);
lean_ctor_set(v___x_2353_, 1, v___x_2355_);
lean_ctor_set(v___x_2353_, 0, v_msgData_2340_);
v___x_2357_ = v___x_2353_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_msgData_2340_);
lean_ctor_set(v_reuseFailAlloc_2365_, 1, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v_msgData_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2358_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2);
v___x_2359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2357_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
v___x_2360_ = l_Lean_MessageData_ofSyntax(v_after_2351_);
v___x_2361_ = l_Lean_indentD(v___x_2360_);
v_msgData_2362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2362_, 0, v___x_2359_);
lean_ctor_set(v_msgData_2362_, 1, v___x_2361_);
v___x_2363_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18(v_msgData_2362_, v_macroStack_2341_);
v___x_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
return v___x_2364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___boxed(lean_object* v_msgData_2368_, lean_object* v_macroStack_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_msgData_2368_, v_macroStack_2369_, v___y_2370_);
lean_dec_ref(v___y_2370_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(lean_object* v_msg_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v_ref_2381_; lean_object* v___x_2382_; lean_object* v_a_2383_; lean_object* v_macroStack_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2395_; 
v_ref_2381_ = lean_ctor_get(v___y_2378_, 2);
v___x_2382_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msg_2373_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_a_2383_);
lean_dec_ref(v___x_2382_);
v_macroStack_2384_ = lean_ctor_get(v___y_2374_, 1);
v___x_2385_ = l_Lean_Elab_getBetterRef(v_ref_2381_, v_macroStack_2384_);
lean_inc(v_macroStack_2384_);
v___x_2386_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_a_2383_, v_macroStack_2384_, v___y_2378_);
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2389_ = v___x_2386_;
v_isShared_2390_ = v_isSharedCheck_2395_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2386_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2395_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2391_; lean_object* v___x_2393_; 
v___x_2391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2385_);
lean_ctor_set(v___x_2391_, 1, v_a_2387_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set_tag(v___x_2389_, 1);
lean_ctor_set(v___x_2389_, 0, v___x_2391_);
v___x_2393_ = v___x_2389_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg___boxed(lean_object* v_msg_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(lean_object* v_ref_2405_, lean_object* v_msg_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_toCold_2414_; lean_object* v_currRecDepth_2415_; lean_object* v_ref_2416_; uint8_t v_diag_2417_; uint8_t v_suppressElabErrors_2418_; lean_object* v_ref_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v_toCold_2414_ = lean_ctor_get(v___y_2411_, 0);
v_currRecDepth_2415_ = lean_ctor_get(v___y_2411_, 1);
v_ref_2416_ = lean_ctor_get(v___y_2411_, 2);
v_diag_2417_ = lean_ctor_get_uint8(v___y_2411_, sizeof(void*)*3);
v_suppressElabErrors_2418_ = lean_ctor_get_uint8(v___y_2411_, sizeof(void*)*3 + 1);
v_ref_2419_ = l_Lean_replaceRef(v_ref_2405_, v_ref_2416_);
lean_inc(v_currRecDepth_2415_);
lean_inc_ref(v_toCold_2414_);
v___x_2420_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2420_, 0, v_toCold_2414_);
lean_ctor_set(v___x_2420_, 1, v_currRecDepth_2415_);
lean_ctor_set(v___x_2420_, 2, v_ref_2419_);
lean_ctor_set_uint8(v___x_2420_, sizeof(void*)*3, v_diag_2417_);
lean_ctor_set_uint8(v___x_2420_, sizeof(void*)*3 + 1, v_suppressElabErrors_2418_);
v___x_2421_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___x_2420_, v___y_2412_);
lean_dec_ref_known(v___x_2420_, 3);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg___boxed(lean_object* v_ref_2422_, lean_object* v_msg_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_ref_2422_, v_msg_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v_ref_2422_);
return v_res_2431_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2432_; double v___x_2433_; 
v___x_2432_ = lean_unsigned_to_nat(0u);
v___x_2433_ = lean_float_of_nat(v___x_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(lean_object* v_cls_2436_, lean_object* v_msg_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_ref_2443_; lean_object* v___x_2444_; lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2489_; 
v_ref_2443_ = lean_ctor_get(v___y_2440_, 2);
v___x_2444_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msg_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2447_ = v___x_2444_;
v_isShared_2448_ = v_isSharedCheck_2489_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2444_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2489_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2449_; lean_object* v_traceState_2450_; lean_object* v_env_2451_; lean_object* v_nextMacroScope_2452_; lean_object* v_ngen_2453_; lean_object* v_auxDeclNGen_2454_; lean_object* v_cache_2455_; lean_object* v_messages_2456_; lean_object* v_infoState_2457_; lean_object* v_snapshotTasks_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2488_; 
v___x_2449_ = lean_st_ref_take(v___y_2441_);
v_traceState_2450_ = lean_ctor_get(v___x_2449_, 4);
v_env_2451_ = lean_ctor_get(v___x_2449_, 0);
v_nextMacroScope_2452_ = lean_ctor_get(v___x_2449_, 1);
v_ngen_2453_ = lean_ctor_get(v___x_2449_, 2);
v_auxDeclNGen_2454_ = lean_ctor_get(v___x_2449_, 3);
v_cache_2455_ = lean_ctor_get(v___x_2449_, 5);
v_messages_2456_ = lean_ctor_get(v___x_2449_, 6);
v_infoState_2457_ = lean_ctor_get(v___x_2449_, 7);
v_snapshotTasks_2458_ = lean_ctor_get(v___x_2449_, 8);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2460_ = v___x_2449_;
v_isShared_2461_ = v_isSharedCheck_2488_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_snapshotTasks_2458_);
lean_inc(v_infoState_2457_);
lean_inc(v_messages_2456_);
lean_inc(v_cache_2455_);
lean_inc(v_traceState_2450_);
lean_inc(v_auxDeclNGen_2454_);
lean_inc(v_ngen_2453_);
lean_inc(v_nextMacroScope_2452_);
lean_inc(v_env_2451_);
lean_dec(v___x_2449_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2488_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
uint64_t v_tid_2462_; lean_object* v_traces_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2487_; 
v_tid_2462_ = lean_ctor_get_uint64(v_traceState_2450_, sizeof(void*)*1);
v_traces_2463_ = lean_ctor_get(v_traceState_2450_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v_traceState_2450_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2465_ = v_traceState_2450_;
v_isShared_2466_ = v_isSharedCheck_2487_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_traces_2463_);
lean_dec(v_traceState_2450_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2487_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2467_; double v___x_2468_; uint8_t v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2477_; 
v___x_2467_ = lean_box(0);
v___x_2468_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0);
v___x_2469_ = 0;
v___x_2470_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_2471_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2471_, 0, v_cls_2436_);
lean_ctor_set(v___x_2471_, 1, v___x_2467_);
lean_ctor_set(v___x_2471_, 2, v___x_2470_);
lean_ctor_set_float(v___x_2471_, sizeof(void*)*3, v___x_2468_);
lean_ctor_set_float(v___x_2471_, sizeof(void*)*3 + 8, v___x_2468_);
lean_ctor_set_uint8(v___x_2471_, sizeof(void*)*3 + 16, v___x_2469_);
v___x_2472_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__1));
v___x_2473_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2471_);
lean_ctor_set(v___x_2473_, 1, v_a_2445_);
lean_ctor_set(v___x_2473_, 2, v___x_2472_);
lean_inc(v_ref_2443_);
v___x_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2474_, 0, v_ref_2443_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
v___x_2475_ = l_Lean_PersistentArray_push___redArg(v_traces_2463_, v___x_2474_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 0, v___x_2475_);
v___x_2477_ = v___x_2465_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2475_);
lean_ctor_set_uint64(v_reuseFailAlloc_2486_, sizeof(void*)*1, v_tid_2462_);
v___x_2477_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
lean_object* v___x_2479_; 
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 4, v___x_2477_);
v___x_2479_ = v___x_2460_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_env_2451_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v_nextMacroScope_2452_);
lean_ctor_set(v_reuseFailAlloc_2485_, 2, v_ngen_2453_);
lean_ctor_set(v_reuseFailAlloc_2485_, 3, v_auxDeclNGen_2454_);
lean_ctor_set(v_reuseFailAlloc_2485_, 4, v___x_2477_);
lean_ctor_set(v_reuseFailAlloc_2485_, 5, v_cache_2455_);
lean_ctor_set(v_reuseFailAlloc_2485_, 6, v_messages_2456_);
lean_ctor_set(v_reuseFailAlloc_2485_, 7, v_infoState_2457_);
lean_ctor_set(v_reuseFailAlloc_2485_, 8, v_snapshotTasks_2458_);
v___x_2479_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2483_; 
v___x_2480_ = lean_st_ref_put(v___y_2441_, v___x_2479_);
v___x_2481_ = lean_box(0);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v___x_2481_);
v___x_2483_ = v___x_2447_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2481_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___boxed(lean_object* v_cls_2490_, lean_object* v_msg_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_2490_, v_msg_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(lean_object* v_as_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
if (lean_obj_tag(v_as_2501_) == 0)
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = lean_box(0);
v___x_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
return v___x_2510_;
}
else
{
lean_object* v_toCold_2511_; lean_object* v_options_2512_; uint8_t v_hasTrace_2513_; 
v_toCold_2511_ = lean_ctor_get(v___y_2506_, 0);
v_options_2512_ = lean_ctor_get(v_toCold_2511_, 2);
v_hasTrace_2513_ = lean_ctor_get_uint8(v_options_2512_, sizeof(void*)*1);
if (v_hasTrace_2513_ == 0)
{
lean_object* v_tail_2514_; 
v_tail_2514_ = lean_ctor_get(v_as_2501_, 1);
lean_inc(v_tail_2514_);
lean_dec_ref_known(v_as_2501_, 2);
v_as_2501_ = v_tail_2514_;
goto _start;
}
else
{
lean_object* v_head_2516_; lean_object* v_tail_2517_; lean_object* v_fst_2518_; lean_object* v_snd_2519_; lean_object* v_inheritedTraceOptions_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; uint8_t v___x_2523_; 
v_head_2516_ = lean_ctor_get(v_as_2501_, 0);
lean_inc(v_head_2516_);
v_tail_2517_ = lean_ctor_get(v_as_2501_, 1);
lean_inc(v_tail_2517_);
lean_dec_ref_known(v_as_2501_, 2);
v_fst_2518_ = lean_ctor_get(v_head_2516_, 0);
lean_inc_n(v_fst_2518_, 2);
v_snd_2519_ = lean_ctor_get(v_head_2516_, 1);
lean_inc(v_snd_2519_);
lean_dec(v_head_2516_);
v_inheritedTraceOptions_2520_ = lean_ctor_get(v_toCold_2511_, 11);
v___x_2521_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__1));
v___x_2522_ = l_Lean_Name_append(v___x_2521_, v_fst_2518_);
v___x_2523_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2520_, v_options_2512_, v___x_2522_);
lean_dec(v___x_2522_);
if (v___x_2523_ == 0)
{
lean_dec(v_snd_2519_);
lean_dec(v_fst_2518_);
v_as_2501_ = v_tail_2517_;
goto _start;
}
else
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2525_, 0, v_snd_2519_);
v___x_2526_ = l_Lean_MessageData_ofFormat(v___x_2525_);
v___x_2527_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_fst_2518_, v___x_2526_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_dec_ref_known(v___x_2527_, 1);
v_as_2501_ = v_tail_2517_;
goto _start;
}
else
{
lean_dec(v_tail_2517_);
return v___x_2527_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___boxed(lean_object* v_as_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(v_as_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
return v_res_2537_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(lean_object* v_keys_2538_, lean_object* v_i_2539_, lean_object* v_k_2540_){
_start:
{
lean_object* v___x_2541_; uint8_t v___x_2542_; 
v___x_2541_ = lean_array_get_size(v_keys_2538_);
v___x_2542_ = lean_nat_dec_lt(v_i_2539_, v___x_2541_);
if (v___x_2542_ == 0)
{
lean_dec(v_i_2539_);
return v___x_2542_;
}
else
{
lean_object* v_k_x27_2543_; uint8_t v___x_2544_; 
v_k_x27_2543_ = lean_array_fget_borrowed(v_keys_2538_, v_i_2539_);
v___x_2544_ = l_Lean_instBEqExtraModUse_beq(v_k_2540_, v_k_x27_2543_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = lean_unsigned_to_nat(1u);
v___x_2546_ = lean_nat_add(v_i_2539_, v___x_2545_);
lean_dec(v_i_2539_);
v_i_2539_ = v___x_2546_;
goto _start;
}
else
{
lean_dec(v_i_2539_);
return v___x_2542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg___boxed(lean_object* v_keys_2548_, lean_object* v_i_2549_, lean_object* v_k_2550_){
_start:
{
uint8_t v_res_2551_; lean_object* v_r_2552_; 
v_res_2551_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_keys_2548_, v_i_2549_, v_k_2550_);
lean_dec_ref(v_k_2550_);
lean_dec_ref(v_keys_2548_);
v_r_2552_ = lean_box(v_res_2551_);
return v_r_2552_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(lean_object* v_x_2553_, size_t v_x_2554_, lean_object* v_x_2555_){
_start:
{
if (lean_obj_tag(v_x_2553_) == 0)
{
lean_object* v_es_2556_; lean_object* v___x_2557_; size_t v___x_2558_; size_t v___x_2559_; lean_object* v_j_2560_; lean_object* v___x_2561_; 
v_es_2556_ = lean_ctor_get(v_x_2553_, 0);
v___x_2557_ = lean_box(2);
v___x_2558_ = ((size_t)31ULL);
v___x_2559_ = lean_usize_land(v_x_2554_, v___x_2558_);
v_j_2560_ = lean_usize_to_nat(v___x_2559_);
v___x_2561_ = lean_array_get_borrowed(v___x_2557_, v_es_2556_, v_j_2560_);
lean_dec(v_j_2560_);
switch(lean_obj_tag(v___x_2561_))
{
case 0:
{
lean_object* v_key_2562_; uint8_t v___x_2563_; 
v_key_2562_ = lean_ctor_get(v___x_2561_, 0);
v___x_2563_ = l_Lean_instBEqExtraModUse_beq(v_x_2555_, v_key_2562_);
return v___x_2563_;
}
case 1:
{
lean_object* v_node_2564_; size_t v___x_2565_; size_t v___x_2566_; 
v_node_2564_ = lean_ctor_get(v___x_2561_, 0);
v___x_2565_ = ((size_t)5ULL);
v___x_2566_ = lean_usize_shift_right(v_x_2554_, v___x_2565_);
v_x_2553_ = v_node_2564_;
v_x_2554_ = v___x_2566_;
goto _start;
}
default: 
{
uint8_t v___x_2568_; 
v___x_2568_ = 0;
return v___x_2568_;
}
}
}
else
{
lean_object* v_ks_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v_ks_2569_ = lean_ctor_get(v_x_2553_, 0);
v___x_2570_ = lean_unsigned_to_nat(0u);
v___x_2571_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_ks_2569_, v___x_2570_, v_x_2555_);
return v___x_2571_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_x_2572_, lean_object* v_x_2573_, lean_object* v_x_2574_){
_start:
{
size_t v_x_14617__boxed_2575_; uint8_t v_res_2576_; lean_object* v_r_2577_; 
v_x_14617__boxed_2575_ = lean_unbox_usize(v_x_2573_);
lean_dec(v_x_2573_);
v_res_2576_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_2572_, v_x_14617__boxed_2575_, v_x_2574_);
lean_dec_ref(v_x_2574_);
lean_dec_ref(v_x_2572_);
v_r_2577_ = lean_box(v_res_2576_);
return v_r_2577_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(lean_object* v_x_2578_, lean_object* v_x_2579_){
_start:
{
uint64_t v___x_2580_; size_t v___x_2581_; uint8_t v___x_2582_; 
v___x_2580_ = l_Lean_instHashableExtraModUse_hash(v_x_2579_);
v___x_2581_ = lean_uint64_to_usize(v___x_2580_);
v___x_2582_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_2578_, v___x_2581_, v_x_2579_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_x_2583_, lean_object* v_x_2584_){
_start:
{
uint8_t v_res_2585_; lean_object* v_r_2586_; 
v_res_2585_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v_x_2583_, v_x_2584_);
lean_dec_ref(v_x_2584_);
lean_dec_ref(v_x_2583_);
v_r_2586_ = lean_box(v_res_2585_);
return v_r_2586_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2589_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1));
v___x_2590_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0));
v___x_2591_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2590_, v___x_2589_);
return v___x_2591_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2592_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4(void){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3);
v___x_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
return v___x_2594_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2595_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4);
v___x_2596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
return v___x_2596_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6(void){
_start:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2597_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4);
v___x_2598_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2597_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
lean_ctor_set(v___x_2598_, 2, v___x_2597_);
lean_ctor_set(v___x_2598_, 3, v___x_2597_);
lean_ctor_set(v___x_2598_, 4, v___x_2597_);
lean_ctor_set(v___x_2598_, 5, v___x_2597_);
return v___x_2598_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10(void){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9));
v___x_2604_ = l_Lean_stringToMessageData(v___x_2603_);
return v___x_2604_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11));
v___x_2607_ = l_Lean_stringToMessageData(v___x_2606_);
return v___x_2607_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13(void){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2608_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_2609_ = l_Lean_stringToMessageData(v___x_2608_);
return v___x_2609_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14(void){
_start:
{
lean_object* v_cls_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v_cls_2610_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__8));
v___x_2611_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__1));
v___x_2612_ = l_Lean_Name_append(v___x_2611_, v_cls_2610_);
return v___x_2612_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15));
v___x_2615_ = l_Lean_stringToMessageData(v___x_2614_);
return v___x_2615_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18(void){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2617_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__17));
v___x_2618_ = l_Lean_stringToMessageData(v___x_2617_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(lean_object* v_mod_2623_, uint8_t v_isMeta_2624_, lean_object* v_hint_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v___x_2633_; lean_object* v_env_2634_; uint8_t v_isExporting_2635_; lean_object* v___x_2636_; lean_object* v_env_2637_; lean_object* v___x_2638_; lean_object* v_entry_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___x_2685_; uint8_t v___x_2686_; 
v___x_2633_ = lean_st_ref_get(v___y_2631_);
v_env_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc_ref(v_env_2634_);
lean_dec(v___x_2633_);
v_isExporting_2635_ = lean_ctor_get_uint8(v_env_2634_, sizeof(void*)*8);
lean_dec_ref(v_env_2634_);
v___x_2636_ = lean_st_ref_get(v___y_2631_);
v_env_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc_ref(v_env_2637_);
lean_dec(v___x_2636_);
v___x_2638_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2);
lean_inc(v_mod_2623_);
v_entry_2639_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2639_, 0, v_mod_2623_);
lean_ctor_set_uint8(v_entry_2639_, sizeof(void*)*1, v_isExporting_2635_);
lean_ctor_set_uint8(v_entry_2639_, sizeof(void*)*1 + 1, v_isMeta_2624_);
v___x_2640_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2641_ = lean_box(1);
v___x_2642_ = lean_box(0);
v___x_2685_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2638_, v___x_2640_, v_env_2637_, v___x_2641_, v___x_2642_);
v___x_2686_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v___x_2685_, v_entry_2639_);
lean_dec(v___x_2685_);
if (v___x_2686_ == 0)
{
lean_object* v_toCold_2687_; lean_object* v_options_2688_; uint8_t v_hasTrace_2689_; 
v_toCold_2687_ = lean_ctor_get(v___y_2630_, 0);
v_options_2688_ = lean_ctor_get(v_toCold_2687_, 2);
v_hasTrace_2689_ = lean_ctor_get_uint8(v_options_2688_, sizeof(void*)*1);
if (v_hasTrace_2689_ == 0)
{
lean_dec(v_hint_2625_);
lean_dec(v_mod_2623_);
v___y_2644_ = v___y_2629_;
v___y_2645_ = v___y_2631_;
goto v___jp_2643_;
}
else
{
lean_object* v_inheritedTraceOptions_2690_; lean_object* v_cls_2691_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___x_2711_; uint8_t v___x_2712_; 
v_inheritedTraceOptions_2690_ = lean_ctor_get(v_toCold_2687_, 11);
v_cls_2691_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__8));
v___x_2711_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14);
v___x_2712_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2690_, v_options_2688_, v___x_2711_);
if (v___x_2712_ == 0)
{
lean_dec(v_hint_2625_);
lean_dec(v_mod_2623_);
v___y_2644_ = v___y_2629_;
v___y_2645_ = v___y_2631_;
goto v___jp_2643_;
}
else
{
lean_object* v___x_2713_; lean_object* v___y_2715_; 
v___x_2713_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16);
if (v_isExporting_2635_ == 0)
{
lean_object* v___x_2722_; 
v___x_2722_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__21));
v___y_2715_ = v___x_2722_;
goto v___jp_2714_;
}
else
{
lean_object* v___x_2723_; 
v___x_2723_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__22));
v___y_2715_ = v___x_2723_;
goto v___jp_2714_;
}
v___jp_2714_:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
lean_inc_ref(v___y_2715_);
v___x_2716_ = l_Lean_stringToMessageData(v___y_2715_);
v___x_2717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2713_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
v___x_2718_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18);
v___x_2719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2717_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
if (v_isMeta_2624_ == 0)
{
lean_object* v___x_2720_; 
v___x_2720_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__19));
v___y_2698_ = v___x_2719_;
v___y_2699_ = v___x_2720_;
goto v___jp_2697_;
}
else
{
lean_object* v___x_2721_; 
v___x_2721_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__20));
v___y_2698_ = v___x_2719_;
v___y_2699_ = v___x_2721_;
goto v___jp_2697_;
}
}
}
v___jp_2692_:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___y_2693_);
lean_ctor_set(v___x_2695_, 1, v___y_2694_);
v___x_2696_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_2691_, v___x_2695_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_dec_ref_known(v___x_2696_, 1);
v___y_2644_ = v___y_2629_;
v___y_2645_ = v___y_2631_;
goto v___jp_2643_;
}
else
{
lean_dec_ref_known(v_entry_2639_, 1);
return v___x_2696_;
}
}
v___jp_2697_:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; uint8_t v___x_2706_; 
lean_inc_ref(v___y_2699_);
v___x_2700_ = l_Lean_stringToMessageData(v___y_2699_);
v___x_2701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___y_2698_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10);
v___x_2703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2701_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = l_Lean_MessageData_ofName(v_mod_2623_);
v___x_2705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2703_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = l_Lean_Name_isAnonymous(v_hint_2625_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2707_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12);
v___x_2708_ = l_Lean_MessageData_ofName(v_hint_2625_);
v___x_2709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___y_2693_ = v___x_2705_;
v___y_2694_ = v___x_2709_;
goto v___jp_2692_;
}
else
{
lean_object* v___x_2710_; 
lean_dec(v_hint_2625_);
v___x_2710_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13);
v___y_2693_ = v___x_2705_;
v___y_2694_ = v___x_2710_;
goto v___jp_2692_;
}
}
}
}
else
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_dec_ref_known(v_entry_2639_, 1);
lean_dec(v_hint_2625_);
lean_dec(v_mod_2623_);
v___x_2724_ = lean_box(0);
v___x_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
return v___x_2725_;
}
v___jp_2643_:
{
lean_object* v___x_2646_; lean_object* v_toEnvExtension_2647_; lean_object* v_env_2648_; lean_object* v_nextMacroScope_2649_; lean_object* v_ngen_2650_; lean_object* v_auxDeclNGen_2651_; lean_object* v_traceState_2652_; lean_object* v_messages_2653_; lean_object* v_infoState_2654_; lean_object* v_snapshotTasks_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2683_; 
v___x_2646_ = lean_st_ref_take(v___y_2645_);
v_toEnvExtension_2647_ = lean_ctor_get(v___x_2640_, 0);
v_env_2648_ = lean_ctor_get(v___x_2646_, 0);
v_nextMacroScope_2649_ = lean_ctor_get(v___x_2646_, 1);
v_ngen_2650_ = lean_ctor_get(v___x_2646_, 2);
v_auxDeclNGen_2651_ = lean_ctor_get(v___x_2646_, 3);
v_traceState_2652_ = lean_ctor_get(v___x_2646_, 4);
v_messages_2653_ = lean_ctor_get(v___x_2646_, 6);
v_infoState_2654_ = lean_ctor_get(v___x_2646_, 7);
v_snapshotTasks_2655_ = lean_ctor_get(v___x_2646_, 8);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2683_ == 0)
{
lean_object* v_unused_2684_; 
v_unused_2684_ = lean_ctor_get(v___x_2646_, 5);
lean_dec(v_unused_2684_);
v___x_2657_ = v___x_2646_;
v_isShared_2658_ = v_isSharedCheck_2683_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_snapshotTasks_2655_);
lean_inc(v_infoState_2654_);
lean_inc(v_messages_2653_);
lean_inc(v_traceState_2652_);
lean_inc(v_auxDeclNGen_2651_);
lean_inc(v_ngen_2650_);
lean_inc(v_nextMacroScope_2649_);
lean_inc(v_env_2648_);
lean_dec(v___x_2646_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2683_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v_asyncMode_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2663_; 
v_asyncMode_2659_ = lean_ctor_get(v_toEnvExtension_2647_, 2);
v___x_2660_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2640_, v_env_2648_, v_entry_2639_, v_asyncMode_2659_, v___x_2642_);
v___x_2661_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 5, v___x_2661_);
lean_ctor_set(v___x_2657_, 0, v___x_2660_);
v___x_2663_ = v___x_2657_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2660_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_nextMacroScope_2649_);
lean_ctor_set(v_reuseFailAlloc_2682_, 2, v_ngen_2650_);
lean_ctor_set(v_reuseFailAlloc_2682_, 3, v_auxDeclNGen_2651_);
lean_ctor_set(v_reuseFailAlloc_2682_, 4, v_traceState_2652_);
lean_ctor_set(v_reuseFailAlloc_2682_, 5, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2682_, 6, v_messages_2653_);
lean_ctor_set(v_reuseFailAlloc_2682_, 7, v_infoState_2654_);
lean_ctor_set(v_reuseFailAlloc_2682_, 8, v_snapshotTasks_2655_);
v___x_2663_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v_mctx_2666_; lean_object* v_zetaDeltaFVarIds_2667_; lean_object* v_postponed_2668_; lean_object* v_diag_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2680_; 
v___x_2664_ = lean_st_ref_put(v___y_2645_, v___x_2663_);
v___x_2665_ = lean_st_ref_take(v___y_2644_);
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
lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2673_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 1, v___x_2673_);
v___x_2675_ = v___x_2671_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_mctx_2666_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v___x_2673_);
lean_ctor_set(v_reuseFailAlloc_2679_, 2, v_zetaDeltaFVarIds_2667_);
lean_ctor_set(v_reuseFailAlloc_2679_, 3, v_postponed_2668_);
lean_ctor_set(v_reuseFailAlloc_2679_, 4, v_diag_2669_);
v___x_2675_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2676_ = lean_st_ref_put(v___y_2644_, v___x_2675_);
v___x_2677_ = lean_box(0);
v___x_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2677_);
return v___x_2678_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___boxed(lean_object* v_mod_2726_, lean_object* v_isMeta_2727_, lean_object* v_hint_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
uint8_t v_isMeta_boxed_2736_; lean_object* v_res_2737_; 
v_isMeta_boxed_2736_ = lean_unbox(v_isMeta_2727_);
v_res_2737_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_mod_2726_, v_isMeta_boxed_2736_, v_hint_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(lean_object* v___x_2738_, lean_object* v_declName_2739_, lean_object* v_as_2740_, size_t v_sz_2741_, size_t v_i_2742_, lean_object* v_b_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
uint8_t v___x_2751_; 
v___x_2751_ = lean_usize_dec_lt(v_i_2742_, v_sz_2741_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; 
lean_dec(v_declName_2739_);
v___x_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2752_, 0, v_b_2743_);
return v___x_2752_;
}
else
{
lean_object* v___x_2753_; lean_object* v_modules_2754_; lean_object* v___x_2755_; lean_object* v_a_2756_; lean_object* v___x_2757_; lean_object* v_toImport_2758_; lean_object* v_module_2759_; uint8_t v___x_2760_; lean_object* v___x_2761_; 
v___x_2753_ = l_Lean_Environment_header(v___x_2738_);
v_modules_2754_ = lean_ctor_get(v___x_2753_, 3);
lean_inc_ref(v_modules_2754_);
lean_dec_ref(v___x_2753_);
v___x_2755_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2756_ = lean_array_uget_borrowed(v_as_2740_, v_i_2742_);
v___x_2757_ = lean_array_get(v___x_2755_, v_modules_2754_, v_a_2756_);
lean_dec_ref(v_modules_2754_);
v_toImport_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc_ref(v_toImport_2758_);
lean_dec(v___x_2757_);
v_module_2759_ = lean_ctor_get(v_toImport_2758_, 0);
lean_inc(v_module_2759_);
lean_dec_ref(v_toImport_2758_);
v___x_2760_ = 0;
lean_inc(v_declName_2739_);
v___x_2761_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_module_2759_, v___x_2760_, v_declName_2739_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v___x_2762_; size_t v___x_2763_; size_t v___x_2764_; 
lean_dec_ref_known(v___x_2761_, 1);
v___x_2762_ = lean_box(0);
v___x_2763_ = ((size_t)1ULL);
v___x_2764_ = lean_usize_add(v_i_2742_, v___x_2763_);
v_i_2742_ = v___x_2764_;
v_b_2743_ = v___x_2762_;
goto _start;
}
else
{
lean_dec(v_declName_2739_);
return v___x_2761_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5___boxed(lean_object* v___x_2766_, lean_object* v_declName_2767_, lean_object* v_as_2768_, lean_object* v_sz_2769_, lean_object* v_i_2770_, lean_object* v_b_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
size_t v_sz_boxed_2779_; size_t v_i_boxed_2780_; lean_object* v_res_2781_; 
v_sz_boxed_2779_ = lean_unbox_usize(v_sz_2769_);
lean_dec(v_sz_2769_);
v_i_boxed_2780_ = lean_unbox_usize(v_i_2770_);
lean_dec(v_i_2770_);
v_res_2781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(v___x_2766_, v_declName_2767_, v_as_2768_, v_sz_boxed_2779_, v_i_boxed_2780_, v_b_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec_ref(v_as_2768_);
lean_dec_ref(v___x_2766_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(lean_object* v_a_2782_, lean_object* v_x_2783_){
_start:
{
if (lean_obj_tag(v_x_2783_) == 0)
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_box(0);
return v___x_2784_;
}
else
{
lean_object* v_key_2785_; lean_object* v_value_2786_; lean_object* v_tail_2787_; uint8_t v___x_2788_; 
v_key_2785_ = lean_ctor_get(v_x_2783_, 0);
v_value_2786_ = lean_ctor_get(v_x_2783_, 1);
v_tail_2787_ = lean_ctor_get(v_x_2783_, 2);
v___x_2788_ = lean_name_eq(v_key_2785_, v_a_2782_);
if (v___x_2788_ == 0)
{
v_x_2783_ = v_tail_2787_;
goto _start;
}
else
{
lean_object* v___x_2790_; 
lean_inc(v_value_2786_);
v___x_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2790_, 0, v_value_2786_);
return v___x_2790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_a_2791_, lean_object* v_x_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(v_a_2791_, v_x_2792_);
lean_dec(v_x_2792_);
lean_dec(v_a_2791_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(lean_object* v_m_2794_, lean_object* v_a_2795_){
_start:
{
lean_object* v_buckets_2796_; lean_object* v___x_2797_; uint64_t v___y_2799_; 
v_buckets_2796_ = lean_ctor_get(v_m_2794_, 1);
v___x_2797_ = lean_array_get_size(v_buckets_2796_);
if (lean_obj_tag(v_a_2795_) == 0)
{
uint64_t v___x_2813_; 
v___x_2813_ = 1723ULL;
v___y_2799_ = v___x_2813_;
goto v___jp_2798_;
}
else
{
uint64_t v_hash_2814_; 
v_hash_2814_ = lean_ctor_get_uint64(v_a_2795_, sizeof(void*)*2);
v___y_2799_ = v_hash_2814_;
goto v___jp_2798_;
}
v___jp_2798_:
{
uint64_t v___x_2800_; uint64_t v___x_2801_; uint64_t v_fold_2802_; uint64_t v___x_2803_; uint64_t v___x_2804_; uint64_t v___x_2805_; size_t v___x_2806_; size_t v___x_2807_; size_t v___x_2808_; size_t v___x_2809_; size_t v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2800_ = 32ULL;
v___x_2801_ = lean_uint64_shift_right(v___y_2799_, v___x_2800_);
v_fold_2802_ = lean_uint64_xor(v___y_2799_, v___x_2801_);
v___x_2803_ = 16ULL;
v___x_2804_ = lean_uint64_shift_right(v_fold_2802_, v___x_2803_);
v___x_2805_ = lean_uint64_xor(v_fold_2802_, v___x_2804_);
v___x_2806_ = lean_uint64_to_usize(v___x_2805_);
v___x_2807_ = lean_usize_of_nat(v___x_2797_);
v___x_2808_ = ((size_t)1ULL);
v___x_2809_ = lean_usize_sub(v___x_2807_, v___x_2808_);
v___x_2810_ = lean_usize_land(v___x_2806_, v___x_2809_);
v___x_2811_ = lean_array_uget_borrowed(v_buckets_2796_, v___x_2810_);
v___x_2812_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(v_a_2795_, v___x_2811_);
return v___x_2812_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_m_2815_, lean_object* v_a_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(v_m_2815_, v_a_2816_);
lean_dec(v_a_2816_);
lean_dec_ref(v_m_2815_);
return v_res_2817_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2820_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__1));
v___x_2821_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0));
v___x_2822_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2821_, v___x_2820_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(lean_object* v_declName_2825_, uint8_t v_isMeta_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v___x_2834_; lean_object* v_env_2838_; lean_object* v___y_2840_; lean_object* v___x_2853_; 
v___x_2834_ = lean_st_ref_get(v___y_2832_);
v_env_2838_ = lean_ctor_get(v___x_2834_, 0);
lean_inc_ref(v_env_2838_);
lean_dec(v___x_2834_);
v___x_2853_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2838_, v_declName_2825_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_dec_ref(v_env_2838_);
lean_dec(v_declName_2825_);
goto v___jp_2835_;
}
else
{
lean_object* v_val_2854_; lean_object* v___x_2855_; lean_object* v_modules_2856_; lean_object* v___x_2857_; uint8_t v___x_2858_; 
v_val_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_val_2854_);
lean_dec_ref_known(v___x_2853_, 1);
v___x_2855_ = l_Lean_Environment_header(v_env_2838_);
v_modules_2856_ = lean_ctor_get(v___x_2855_, 3);
lean_inc_ref(v_modules_2856_);
lean_dec_ref(v___x_2855_);
v___x_2857_ = lean_array_get_size(v_modules_2856_);
v___x_2858_ = lean_nat_dec_lt(v_val_2854_, v___x_2857_);
if (v___x_2858_ == 0)
{
lean_dec_ref(v_modules_2856_);
lean_dec(v_val_2854_);
lean_dec_ref(v_env_2838_);
lean_dec(v_declName_2825_);
goto v___jp_2835_;
}
else
{
lean_object* v___x_2859_; lean_object* v_env_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; uint8_t v___y_2864_; 
v___x_2859_ = lean_st_ref_get(v___y_2832_);
v_env_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc_ref(v_env_2860_);
lean_dec(v___x_2859_);
v___x_2861_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__2);
v___x_2862_ = lean_array_fget(v_modules_2856_, v_val_2854_);
lean_dec(v_val_2854_);
lean_dec_ref(v_modules_2856_);
if (v_isMeta_2826_ == 0)
{
lean_dec_ref(v_env_2860_);
v___y_2864_ = v_isMeta_2826_;
goto v___jp_2863_;
}
else
{
uint8_t v___x_2875_; 
lean_inc(v_declName_2825_);
v___x_2875_ = l_Lean_isMarkedMeta(v_env_2860_, v_declName_2825_);
if (v___x_2875_ == 0)
{
v___y_2864_ = v_isMeta_2826_;
goto v___jp_2863_;
}
else
{
uint8_t v___x_2876_; 
v___x_2876_ = 0;
v___y_2864_ = v___x_2876_;
goto v___jp_2863_;
}
}
v___jp_2863_:
{
lean_object* v_toImport_2865_; lean_object* v_module_2866_; lean_object* v___x_2867_; 
v_toImport_2865_ = lean_ctor_get(v___x_2862_, 0);
lean_inc_ref(v_toImport_2865_);
lean_dec(v___x_2862_);
v_module_2866_ = lean_ctor_get(v_toImport_2865_, 0);
lean_inc(v_module_2866_);
lean_dec_ref(v_toImport_2865_);
lean_inc(v_declName_2825_);
v___x_2867_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_module_2866_, v___y_2864_, v_declName_2825_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
lean_dec_ref_known(v___x_2867_, 1);
v___x_2868_ = l_Lean_indirectModUseExt;
v___x_2869_ = lean_box(1);
v___x_2870_ = lean_box(0);
lean_inc_ref(v_env_2838_);
v___x_2871_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2861_, v___x_2868_, v_env_2838_, v___x_2869_, v___x_2870_);
v___x_2872_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(v___x_2871_, v_declName_2825_);
lean_dec(v___x_2871_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v___x_2873_; 
v___x_2873_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__3));
v___y_2840_ = v___x_2873_;
goto v___jp_2839_;
}
else
{
lean_object* v_val_2874_; 
v_val_2874_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_val_2874_);
lean_dec_ref_known(v___x_2872_, 1);
v___y_2840_ = v_val_2874_;
goto v___jp_2839_;
}
}
else
{
lean_dec_ref(v_env_2838_);
lean_dec(v_declName_2825_);
return v___x_2867_;
}
}
}
}
v___jp_2835_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = lean_box(0);
v___x_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
return v___x_2837_;
}
v___jp_2839_:
{
lean_object* v___x_2841_; size_t v_sz_2842_; size_t v___x_2843_; lean_object* v___x_2844_; 
v___x_2841_ = lean_box(0);
v_sz_2842_ = lean_array_size(v___y_2840_);
v___x_2843_ = ((size_t)0ULL);
v___x_2844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(v_env_2838_, v_declName_2825_, v___y_2840_, v_sz_2842_, v___x_2843_, v___x_2841_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
lean_dec_ref(v___y_2840_);
lean_dec_ref(v_env_2838_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2851_ == 0)
{
lean_object* v_unused_2852_; 
v_unused_2852_ = lean_ctor_get(v___x_2844_, 0);
lean_dec(v_unused_2852_);
v___x_2846_ = v___x_2844_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_dec(v___x_2844_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v___x_2841_);
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2841_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
else
{
return v___x_2844_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___boxed(lean_object* v_declName_2877_, lean_object* v_isMeta_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
uint8_t v_isMeta_boxed_2886_; lean_object* v_res_2887_; 
v_isMeta_boxed_2886_ = lean_unbox(v_isMeta_2878_);
v_res_2887_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(v_declName_2877_, v_isMeta_boxed_2886_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(lean_object* v_as_x27_2888_, lean_object* v_b_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
if (lean_obj_tag(v_as_x27_2888_) == 0)
{
lean_object* v___x_2897_; 
v___x_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2897_, 0, v_b_2889_);
return v___x_2897_;
}
else
{
lean_object* v_head_2898_; lean_object* v_tail_2899_; uint8_t v___x_2900_; lean_object* v___x_2901_; 
v_head_2898_ = lean_ctor_get(v_as_x27_2888_, 0);
v_tail_2899_ = lean_ctor_get(v_as_x27_2888_, 1);
v___x_2900_ = 1;
lean_inc(v_head_2898_);
v___x_2901_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(v_head_2898_, v___x_2900_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v___x_2902_; 
lean_dec_ref_known(v___x_2901_, 1);
v___x_2902_ = lean_box(0);
v_as_x27_2888_ = v_tail_2899_;
v_b_2889_ = v___x_2902_;
goto _start;
}
else
{
return v___x_2901_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2904_, lean_object* v_b_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_as_x27_2904_, v_b_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v_as_x27_2904_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4(lean_object* v_env_2914_, lean_object* v_options_2915_, lean_object* v_currNamespace_2916_, lean_object* v_openDecls_2917_, lean_object* v_n_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2921_ = l_Lean_ResolveName_resolveGlobalName(v_env_2914_, v_options_2915_, v_currNamespace_2916_, v_openDecls_2917_, v_n_2918_);
v___x_2922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
lean_ctor_set(v___x_2922_, 1, v___y_2920_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4___boxed(lean_object* v_env_2923_, lean_object* v_options_2924_, lean_object* v_currNamespace_2925_, lean_object* v_openDecls_2926_, lean_object* v_n_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4(v_env_2923_, v_options_2924_, v_currNamespace_2925_, v_openDecls_2926_, v_n_2927_, v___y_2928_, v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec_ref(v_options_2924_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2(lean_object* v_env_2931_, lean_object* v_currNamespace_2932_, lean_object* v_openDecls_2933_, lean_object* v_n_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2937_ = l_Lean_ResolveName_resolveNamespace(v_env_2931_, v_currNamespace_2932_, v_openDecls_2933_, v_n_2934_);
v___x_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
lean_ctor_set(v___x_2938_, 1, v___y_2936_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2___boxed(lean_object* v_env_2939_, lean_object* v_currNamespace_2940_, lean_object* v_openDecls_2941_, lean_object* v_n_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2(v_env_2939_, v_currNamespace_2940_, v_openDecls_2941_, v_n_2942_, v___y_2943_, v___y_2944_);
lean_dec_ref(v___y_2943_);
return v_res_2945_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2946_ = lean_box(0);
v___x_2947_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
lean_ctor_set(v___x_2948_, 1, v___x_2946_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg(){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0);
v___x_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___boxed(lean_object* v___y_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
return v_res_2953_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2959_ = l_Lean_maxRecDepthErrorMessage;
v___x_2960_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
return v___x_2960_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2961_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3);
v___x_2962_ = l_Lean_MessageData_ofFormat(v___x_2961_);
return v___x_2962_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2963_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4);
v___x_2964_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__2));
v___x_2965_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
lean_ctor_set(v___x_2965_, 1, v___x_2963_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(lean_object* v_ref_2966_){
_start:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2968_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5);
v___x_2969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2969_, 0, v_ref_2966_);
lean_ctor_set(v___x_2969_, 1, v___x_2968_);
v___x_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_ref_2971_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(lean_object* v_x_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v___x_2983_; lean_object* v_toCold_2984_; lean_object* v_env_2985_; lean_object* v_currRecDepth_2986_; lean_object* v_ref_2987_; lean_object* v_options_2988_; lean_object* v_maxRecDepth_2989_; lean_object* v_currNamespace_2990_; lean_object* v_openDecls_2991_; lean_object* v_quotContext_2992_; lean_object* v_currMacroScope_2993_; lean_object* v___x_2994_; lean_object* v_nextMacroScope_2995_; lean_object* v___f_2996_; lean_object* v___f_2997_; lean_object* v___f_2998_; lean_object* v___f_2999_; lean_object* v___f_3000_; lean_object* v_methods_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_2983_ = lean_st_ref_get(v___y_2981_);
v_toCold_2984_ = lean_ctor_get(v___y_2980_, 0);
v_env_2985_ = lean_ctor_get(v___x_2983_, 0);
lean_inc_ref_n(v_env_2985_, 4);
lean_dec(v___x_2983_);
v_currRecDepth_2986_ = lean_ctor_get(v___y_2980_, 1);
v_ref_2987_ = lean_ctor_get(v___y_2980_, 2);
v_options_2988_ = lean_ctor_get(v_toCold_2984_, 2);
v_maxRecDepth_2989_ = lean_ctor_get(v_toCold_2984_, 3);
v_currNamespace_2990_ = lean_ctor_get(v_toCold_2984_, 4);
v_openDecls_2991_ = lean_ctor_get(v_toCold_2984_, 5);
v_quotContext_2992_ = lean_ctor_get(v_toCold_2984_, 8);
v_currMacroScope_2993_ = lean_ctor_get(v_toCold_2984_, 9);
v___x_2994_ = lean_st_ref_get(v___y_2981_);
v_nextMacroScope_2995_ = lean_ctor_get(v___x_2994_, 1);
lean_inc(v_nextMacroScope_2995_);
lean_dec(v___x_2994_);
v___f_2996_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2996_, 0, v_env_2985_);
v___f_2997_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2997_, 0, v_env_2985_);
lean_inc_n(v_openDecls_2991_, 2);
lean_inc_n(v_currNamespace_2990_, 3);
v___f_2998_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_2998_, 0, v_env_2985_);
lean_closure_set(v___f_2998_, 1, v_currNamespace_2990_);
lean_closure_set(v___f_2998_, 2, v_openDecls_2991_);
v___f_2999_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2999_, 0, v_currNamespace_2990_);
lean_inc_ref(v_options_2988_);
v___f_3000_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_3000_, 0, v_env_2985_);
lean_closure_set(v___f_3000_, 1, v_options_2988_);
lean_closure_set(v___f_3000_, 2, v_currNamespace_2990_);
lean_closure_set(v___f_3000_, 3, v_openDecls_2991_);
v_methods_3001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_3001_, 0, v___f_2996_);
lean_ctor_set(v_methods_3001_, 1, v___f_2999_);
lean_ctor_set(v_methods_3001_, 2, v___f_2997_);
lean_ctor_set(v_methods_3001_, 3, v___f_2998_);
lean_ctor_set(v_methods_3001_, 4, v___f_3000_);
lean_inc(v_ref_2987_);
lean_inc(v_maxRecDepth_2989_);
lean_inc(v_currRecDepth_2986_);
lean_inc(v_currMacroScope_2993_);
lean_inc(v_quotContext_2992_);
v___x_3002_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3002_, 0, v_methods_3001_);
lean_ctor_set(v___x_3002_, 1, v_quotContext_2992_);
lean_ctor_set(v___x_3002_, 2, v_currMacroScope_2993_);
lean_ctor_set(v___x_3002_, 3, v_currRecDepth_2986_);
lean_ctor_set(v___x_3002_, 4, v_maxRecDepth_2989_);
lean_ctor_set(v___x_3002_, 5, v_ref_2987_);
v___x_3003_ = lean_box(0);
v___x_3004_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3004_, 0, v_nextMacroScope_2995_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
lean_ctor_set(v___x_3004_, 2, v___x_3003_);
v___x_3005_ = lean_apply_2(v_x_2975_, v___x_3002_, v___x_3004_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v_a_3007_; lean_object* v_macroScope_3008_; lean_object* v_traceMsgs_3009_; lean_object* v_expandedMacroDecls_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 1);
lean_inc(v_a_3006_);
v_a_3007_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3005_, 2);
v_macroScope_3008_ = lean_ctor_get(v_a_3006_, 0);
lean_inc(v_macroScope_3008_);
v_traceMsgs_3009_ = lean_ctor_get(v_a_3006_, 1);
lean_inc(v_traceMsgs_3009_);
v_expandedMacroDecls_3010_ = lean_ctor_get(v_a_3006_, 2);
lean_inc(v_expandedMacroDecls_3010_);
lean_dec(v_a_3006_);
v___x_3011_ = lean_box(0);
v___x_3012_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_expandedMacroDecls_3010_, v___x_3011_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
lean_dec(v_expandedMacroDecls_3010_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v___x_3013_; lean_object* v_env_3014_; lean_object* v_ngen_3015_; lean_object* v_auxDeclNGen_3016_; lean_object* v_traceState_3017_; lean_object* v_cache_3018_; lean_object* v_messages_3019_; lean_object* v_infoState_3020_; lean_object* v_snapshotTasks_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3047_; 
lean_dec_ref_known(v___x_3012_, 1);
v___x_3013_ = lean_st_ref_take(v___y_2981_);
v_env_3014_ = lean_ctor_get(v___x_3013_, 0);
v_ngen_3015_ = lean_ctor_get(v___x_3013_, 2);
v_auxDeclNGen_3016_ = lean_ctor_get(v___x_3013_, 3);
v_traceState_3017_ = lean_ctor_get(v___x_3013_, 4);
v_cache_3018_ = lean_ctor_get(v___x_3013_, 5);
v_messages_3019_ = lean_ctor_get(v___x_3013_, 6);
v_infoState_3020_ = lean_ctor_get(v___x_3013_, 7);
v_snapshotTasks_3021_ = lean_ctor_get(v___x_3013_, 8);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3047_ == 0)
{
lean_object* v_unused_3048_; 
v_unused_3048_ = lean_ctor_get(v___x_3013_, 1);
lean_dec(v_unused_3048_);
v___x_3023_ = v___x_3013_;
v_isShared_3024_ = v_isSharedCheck_3047_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_snapshotTasks_3021_);
lean_inc(v_infoState_3020_);
lean_inc(v_messages_3019_);
lean_inc(v_cache_3018_);
lean_inc(v_traceState_3017_);
lean_inc(v_auxDeclNGen_3016_);
lean_inc(v_ngen_3015_);
lean_inc(v_env_3014_);
lean_dec(v___x_3013_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3047_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 1, v_macroScope_3008_);
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_env_3014_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v_macroScope_3008_);
lean_ctor_set(v_reuseFailAlloc_3046_, 2, v_ngen_3015_);
lean_ctor_set(v_reuseFailAlloc_3046_, 3, v_auxDeclNGen_3016_);
lean_ctor_set(v_reuseFailAlloc_3046_, 4, v_traceState_3017_);
lean_ctor_set(v_reuseFailAlloc_3046_, 5, v_cache_3018_);
lean_ctor_set(v_reuseFailAlloc_3046_, 6, v_messages_3019_);
lean_ctor_set(v_reuseFailAlloc_3046_, 7, v_infoState_3020_);
lean_ctor_set(v_reuseFailAlloc_3046_, 8, v_snapshotTasks_3021_);
v___x_3026_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3027_ = lean_st_ref_put(v___y_2981_, v___x_3026_);
v___x_3028_ = l_List_reverse___redArg(v_traceMsgs_3009_);
v___x_3029_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(v___x_3028_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3036_ == 0)
{
lean_object* v_unused_3037_; 
v_unused_3037_ = lean_ctor_get(v___x_3029_, 0);
lean_dec(v_unused_3037_);
v___x_3031_ = v___x_3029_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_dec(v___x_3029_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 0, v_a_3007_);
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3007_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec(v_a_3007_);
v_a_3038_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3029_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3029_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_dec(v_traceMsgs_3009_);
lean_dec(v_macroScope_3008_);
lean_dec(v_a_3007_);
v_a_3049_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_3012_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3012_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
else
{
lean_object* v_a_3057_; 
v_a_3057_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3057_);
lean_dec_ref_known(v___x_3005_, 2);
if (lean_obj_tag(v_a_3057_) == 0)
{
lean_object* v_a_3058_; lean_object* v_a_3059_; lean_object* v___x_3060_; uint8_t v___x_3061_; 
v_a_3058_ = lean_ctor_get(v_a_3057_, 0);
lean_inc(v_a_3058_);
v_a_3059_ = lean_ctor_get(v_a_3057_, 1);
lean_inc_ref(v_a_3059_);
lean_dec_ref_known(v_a_3057_, 2);
v___x_3060_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___closed__0));
v___x_3061_ = lean_string_dec_eq(v_a_3059_, v___x_3060_);
if (v___x_3061_ == 0)
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3062_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3062_, 0, v_a_3059_);
v___x_3063_ = l_Lean_MessageData_ofFormat(v___x_3062_);
v___x_3064_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_a_3058_, v___x_3063_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
lean_dec(v_a_3058_);
return v___x_3064_;
}
else
{
lean_object* v___x_3065_; 
lean_dec_ref(v_a_3059_);
v___x_3065_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_a_3058_);
return v___x_3065_;
}
}
else
{
lean_object* v___x_3066_; 
v___x_3066_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
return v___x_3066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___boxed(lean_object* v_x_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v_x_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(lean_object* v_pre_3076_, lean_object* v_binders_3077_, lean_object* v_type_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
lean_object* v___y_3087_; lean_object* v___f_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
lean_inc_ref(v_pre_3076_);
v___f_3091_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1___boxed), 10, 2);
lean_closure_set(v___f_3091_, 0, v_type_3078_);
lean_closure_set(v___f_3091_, 1, v_pre_3076_);
v___x_3092_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___boxed), 10, 3);
lean_closure_set(v___x_3092_, 0, lean_box(0));
lean_closure_set(v___x_3092_, 1, v_binders_3077_);
lean_closure_set(v___x_3092_, 2, v___f_3091_);
v___x_3093_ = l_Lean_Elab_Term_withAutoBoundImplicit___redArg(v___x_3092_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_dec_ref(v_pre_3076_);
v___y_3087_ = v___x_3093_;
goto v___jp_3086_;
}
else
{
lean_object* v_a_3094_; uint8_t v___y_3096_; uint8_t v___x_3100_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_a_3094_);
v___x_3100_ = l_Lean_Exception_isInterrupt(v_a_3094_);
if (v___x_3100_ == 0)
{
uint8_t v___x_3101_; 
v___x_3101_ = l_Lean_Exception_isRuntime(v_a_3094_);
v___y_3096_ = v___x_3101_;
goto v___jp_3095_;
}
else
{
lean_dec(v_a_3094_);
v___y_3096_ = v___x_3100_;
goto v___jp_3095_;
}
v___jp_3095_:
{
if (v___y_3096_ == 0)
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
lean_dec_ref_known(v___x_3093_, 1);
v___x_3097_ = lean_box(0);
v___x_3098_ = l_Lean_Name_str___override(v___x_3097_, v_pre_3076_);
v___x_3099_ = l_Lean_Core_mkFreshUserName(v___x_3098_, v_a_3083_, v_a_3084_);
v___y_3087_ = v___x_3099_;
goto v___jp_3086_;
}
else
{
lean_dec_ref(v_pre_3076_);
v___y_3087_ = v___x_3093_;
goto v___jp_3086_;
}
}
}
v___jp_3086_:
{
if (lean_obj_tag(v___y_3087_) == 0)
{
lean_object* v_a_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v_a_3088_ = lean_ctor_get(v___y_3087_, 0);
lean_inc(v_a_3088_);
lean_dec_ref_known(v___y_3087_, 1);
v___x_3089_ = lean_alloc_closure((void*)(l_Lean_Elab_mkUnusedBaseName___boxed), 3, 1);
lean_closure_set(v___x_3089_, 0, v_a_3088_);
v___x_3090_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v___x_3089_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
return v___x_3090_;
}
else
{
return v___y_3087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___boxed(lean_object* v_pre_3102_, lean_object* v_binders_3103_, lean_object* v_type_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(v_pre_3102_, v_binders_3103_, v_type_3104_, v_a_3105_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3109_, v_a_3110_);
lean_dec(v_a_3110_);
lean_dec_ref(v_a_3109_);
lean_dec(v_a_3108_);
lean_dec_ref(v_a_3107_);
lean_dec(v_a_3106_);
lean_dec_ref(v_a_3105_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2(lean_object* v_00_u03b1_3113_, lean_object* v_x_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v___x_3117_; 
v___x_3117_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v_x_3114_, v___y_3116_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3118_, lean_object* v_x_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2(v_00_u03b1_3118_, v_x_3119_, v___y_3120_, v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec_ref(v_x_3119_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7(lean_object* v_00_u03b1_3123_, lean_object* v_ref_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_){
_start:
{
lean_object* v___x_3132_; 
v___x_3132_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_ref_3124_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___boxed(lean_object* v_00_u03b1_3133_, lean_object* v_ref_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7(v_00_u03b1_3133_, v_ref_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8(lean_object* v_00_u03b1_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___boxed(lean_object* v_00_u03b1_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8(v_00_u03b1_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1(lean_object* v_00_u03b1_3161_, lean_object* v_x_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
lean_object* v___x_3170_; 
v___x_3170_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v_x_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___boxed(lean_object* v_00_u03b1_3171_, lean_object* v_x_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v_res_3180_; 
v_res_3180_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1(v_00_u03b1_3171_, v_x_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1(lean_object* v_cls_3181_, lean_object* v_msg_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v___x_3190_; 
v___x_3190_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_3181_, v_msg_3182_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___boxed(lean_object* v_cls_3191_, lean_object* v_msg_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
lean_object* v_res_3200_; 
v_res_3200_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1(v_cls_3191_, v_msg_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4(lean_object* v_as_3201_, lean_object* v_as_x27_3202_, lean_object* v_b_3203_, lean_object* v_a_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v___x_3212_; 
v___x_3212_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_as_x27_3202_, v_b_3203_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___boxed(lean_object* v_as_3213_, lean_object* v_as_x27_3214_, lean_object* v_b_3215_, lean_object* v_a_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4(v_as_3213_, v_as_x27_3214_, v_b_3215_, v_a_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v_as_x27_3214_);
lean_dec(v_as_3213_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6(lean_object* v_00_u03b1_3225_, lean_object* v_ref_3226_, lean_object* v_msg_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v___x_3235_; 
v___x_3235_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_ref_3226_, v_msg_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3236_, lean_object* v_ref_3237_, lean_object* v_msg_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6(v_00_u03b1_3236_, v_ref_3237_, v_msg_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v_ref_3237_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_3247_, lean_object* v_m_3248_, lean_object* v_a_3249_){
_start:
{
lean_object* v___x_3250_; 
v___x_3250_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(v_m_3248_, v_a_3249_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3251_, lean_object* v_m_3252_, lean_object* v_a_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6(v_00_u03b2_3251_, v_m_3252_, v_a_3253_);
lean_dec(v_a_3253_);
lean_dec_ref(v_m_3252_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10(lean_object* v_00_u03b1_3255_, lean_object* v_msg_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___boxed(lean_object* v_00_u03b1_3265_, lean_object* v_msg_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10(v_00_u03b1_3265_, v_msg_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
return v_res_3274_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_3275_, lean_object* v_x_3276_, lean_object* v_x_3277_){
_start:
{
uint8_t v___x_3278_; 
v___x_3278_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v_x_3276_, v_x_3277_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3279_, lean_object* v_x_3280_, lean_object* v_x_3281_){
_start:
{
uint8_t v_res_3282_; lean_object* v_r_3283_; 
v_res_3282_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7(v_00_u03b2_3279_, v_x_3280_, v_x_3281_);
lean_dec_ref(v_x_3281_);
lean_dec_ref(v_x_3280_);
v_r_3283_ = lean_box(v_res_3282_);
return v_r_3283_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_3284_, lean_object* v_a_3285_, lean_object* v_x_3286_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(v_a_3285_, v_x_3286_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_3288_, lean_object* v_a_3289_, lean_object* v_x_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_3288_, v_a_3289_, v_x_3290_);
lean_dec(v_x_3290_);
lean_dec(v_a_3289_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15(lean_object* v_msgData_3292_, lean_object* v_macroStack_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v___x_3301_; 
v___x_3301_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_msgData_3292_, v_macroStack_3293_, v___y_3298_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___boxed(lean_object* v_msgData_3302_, lean_object* v_macroStack_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15(v_msgData_3302_, v_macroStack_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
return v_res_3311_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_3312_, lean_object* v_x_3313_, size_t v_x_3314_, lean_object* v_x_3315_){
_start:
{
uint8_t v___x_3316_; 
v___x_3316_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_3313_, v_x_3314_, v_x_3315_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3317_, lean_object* v_x_3318_, lean_object* v_x_3319_, lean_object* v_x_3320_){
_start:
{
size_t v_x_15695__boxed_3321_; uint8_t v_res_3322_; lean_object* v_r_3323_; 
v_x_15695__boxed_3321_ = lean_unbox_usize(v_x_3319_);
lean_dec(v_x_3319_);
v_res_3322_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11(v_00_u03b2_3317_, v_x_3318_, v_x_15695__boxed_3321_, v_x_3320_);
lean_dec_ref(v_x_3320_);
lean_dec_ref(v_x_3318_);
v_r_3323_ = lean_box(v_res_3322_);
return v_r_3323_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15(lean_object* v_00_u03b2_3324_, lean_object* v_keys_3325_, lean_object* v_vals_3326_, lean_object* v_heq_3327_, lean_object* v_i_3328_, lean_object* v_k_3329_){
_start:
{
uint8_t v___x_3330_; 
v___x_3330_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_keys_3325_, v_i_3328_, v_k_3329_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___boxed(lean_object* v_00_u03b2_3331_, lean_object* v_keys_3332_, lean_object* v_vals_3333_, lean_object* v_heq_3334_, lean_object* v_i_3335_, lean_object* v_k_3336_){
_start:
{
uint8_t v_res_3337_; lean_object* v_r_3338_; 
v_res_3337_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15(v_00_u03b2_3331_, v_keys_3332_, v_vals_3333_, v_heq_3334_, v_i_3335_, v_k_3336_);
lean_dec_ref(v_k_3336_);
lean_dec_ref(v_vals_3333_);
lean_dec_ref(v_keys_3332_);
v_r_3338_ = lean_box(v_res_3337_);
return v_r_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__0(lean_object* v_binders_3340_, lean_object* v_type_3341_, lean_object* v_x_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3350_ = ((lean_object*)(l_Lean_Elab_Command_mkInstanceName___lam__0___closed__0));
v___x_3351_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(v___x_3350_, v_binders_3340_, v_type_3341_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__0___boxed(lean_object* v_binders_3352_, lean_object* v_type_3353_, lean_object* v_x_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l_Lean_Elab_Command_mkInstanceName___lam__0(v_binders_3352_, v_type_3353_, v_x_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec_ref(v_x_3354_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__1(lean_object* v_a_3363_, lean_object* v_val_3364_, lean_object* v_a_x3f_3365_){
_start:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3367_ = lean_st_ref_swap(v_a_3363_, v_val_3364_);
lean_dec(v___x_3367_);
v___x_3368_ = lean_box(0);
v___x_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__1___boxed(lean_object* v_a_3370_, lean_object* v_val_3371_, lean_object* v_a_x3f_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l_Lean_Elab_Command_mkInstanceName___lam__1(v_a_3370_, v_val_3371_, v_a_x3f_3372_);
lean_dec(v_a_x3f_3372_);
lean_dec(v_a_3370_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName(lean_object* v_binders_3375_, lean_object* v_type_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_){
_start:
{
lean_object* v___x_3380_; lean_object* v___f_3381_; lean_object* v_r_3382_; 
v___x_3380_ = lean_st_ref_get(v_a_3378_);
v___f_3381_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkInstanceName___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3381_, 0, v_binders_3375_);
lean_closure_set(v___f_3381_, 1, v_type_3376_);
v_r_3382_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_3381_, v_a_3377_, v_a_3378_);
if (lean_obj_tag(v_r_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3399_; 
v_a_3383_ = lean_ctor_get(v_r_3382_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v_r_3382_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3385_ = v_r_3382_;
v_isShared_3386_ = v_isSharedCheck_3399_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v_r_3382_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3399_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
lean_inc(v_a_3383_);
if (v_isShared_3386_ == 0)
{
lean_ctor_set_tag(v___x_3385_, 1);
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
lean_object* v___x_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
v___x_3389_ = l_Lean_Elab_Command_mkInstanceName___lam__1(v_a_3378_, v___x_3380_, v___x_3388_);
lean_dec_ref(v___x_3388_);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3396_ == 0)
{
lean_object* v_unused_3397_; 
v_unused_3397_ = lean_ctor_get(v___x_3389_, 0);
lean_dec(v_unused_3397_);
v___x_3391_ = v___x_3389_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_dec(v___x_3389_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 0, v_a_3383_);
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3383_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
v_a_3400_ = lean_ctor_get(v_r_3382_, 0);
lean_inc(v_a_3400_);
lean_dec_ref_known(v_r_3382_, 1);
v___x_3401_ = lean_box(0);
v___x_3402_ = l_Lean_Elab_Command_mkInstanceName___lam__1(v_a_3378_, v___x_3380_, v___x_3401_);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3409_ == 0)
{
lean_object* v_unused_3410_; 
v_unused_3410_ = lean_ctor_get(v___x_3402_, 0);
lean_dec(v_unused_3410_);
v___x_3404_ = v___x_3402_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_dec(v___x_3402_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
lean_ctor_set_tag(v___x_3404_, 1);
lean_ctor_set(v___x_3404_, 0, v_a_3400_);
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3400_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___boxed(lean_object* v_binders_3411_, lean_object* v_type_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l_Lean_Elab_Command_mkInstanceName(v_binders_3411_, v_type_3412_, v_a_3413_, v_a_3414_);
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3413_);
return v_res_3416_;
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
